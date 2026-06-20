import os
import sys
import urllib.request, urllib.error, urllib.parse
import copy
import threading
import time
import math
import tempfile
import base64
import hashlib
import socket
import logging
from io import StringIO
import multiprocessing.dummy as multiprocessing
from ctypes import c_int
import json
import ssl

from . import utils
from .control_thread import ControlThread
from .download import download

__all__ = ['SmartDL', 'utils']

__version_mjaor__ = 1
__version_minor__ = 3
__version_micro__ = 4
__version__ = "{}.{}.{}".format(__version_mjaor__, __version_minor__, __version_micro__)


class HashFailedException(Exception):
    "Raised when hash check fails."
    def __init__(self, fn, calc_hash, needed_hash):
        self.filename = fn
        self.calculated_hash = calc_hash
        self.needed_hash = needed_hash

    def __str__(self):
        return 'HashFailedException({}, got {}, expected {})'.format(self.filename, self.calculated_hash, self.needed_hash)

    def __repr__(self):
        return '<HashFailedException {}, got {}, expected {}>'.format(self.filename, self.calculated_hash, self.needed_hash)


class CanceledException(Exception):
    "Raised when the job is canceled."
    def __init__(self):
        pass

    def __str__(self):
        return 'CanceledException'

    def __repr__(self):
        return "<CanceledException>"


class SmartDL:
    '''
    The main SmartDL class

    :param urls: Download url. It is possible to pass unsafe and unicode characters. You can also pass a list of urls, and those will be used as mirrors.
    :type urls: string or list of strings

    :param dest: Destination path. Default is `%TEMP%/pySmartDL/`.
    :type dest: string

    :param progress_bar: If True, prints a progress bar to the `stdout stream <http://docs.python.org/2/library/sys.html#sys.stdout>`_. Default is `True`.
    :type progress_bar: bool

    :param fix_urls: If true, attempts to fix urls with unsafe characters.
    :type fix_urls: bool

    :param threads: Number of threads to use.
    :type threads: int

    :param timeout: Timeout for network operations, in seconds. Default is 5.
    :type timeout: int

    :param logger: An optional logger.
    :type logger: `logging.Logger` instance

    :param connect_default_logger: If true, connects a default logger to the class.
    :type connect_default_logger: bool

    :param request_args: Arguments to be passed to a new urllib.request.Request instance in dictionary form.
    :type request_args: dict

    :param verify: If ssl certificates should be validated.
    :type verify: bool

    :param proxies: A dictionary of proxy settings. Supports http and https keys.
                    Example: {'http': 'http://user:pass@proxy:8080', 'https': 'http://user:pass@proxy:8080'}
                    Also supports SOCKS proxies if PySocks is installed:
                    {'http': 'socks5://user:pass@proxy:1080', 'https': 'socks5://user:pass@proxy:1080'}
    :type proxies: dict or None

    .. NOTE::
            The provided dest may be a folder or a full path name (including filename). The workflow is:

            * If the path exists, and it's an existing folder, the file will be downloaded to there with the original filename.
            * If the past does not exist, it will create the folders, if needed, and refer to the last section of the path as the filename.
            * If you want to download to folder that does not exist at the moment, and want the module to fill in the filename, make sure the path ends with `os.sep`.
            * If no path is provided, `%TEMP%/pySmartDL/` will be used.
    '''

    def __init__(self, urls, dest=None, progress_bar=True, fix_urls=True, threads=5,
                 timeout=5, logger=None, connect_default_logger=False,
                 request_args=None, verify=True, proxies=None):

        if logger:
            self.logger = logger
        elif connect_default_logger:
            self.logger = utils.create_debugging_logger()
        else:
            self.logger = utils.DummyLogger()

        if request_args:
            if "headers" not in request_args:
                request_args["headers"] = dict()
            self.requestArgs = request_args
        else:
            self.requestArgs = {"headers": dict()}

        if "User-Agent" not in self.requestArgs["headers"]:
            self.requestArgs["headers"]["User-Agent"] = utils.get_random_useragent()

        # ── Proxy support ──────────────────────────────────────────────────────
        self.proxies = proxies
        if proxies:
            self._apply_proxy(proxies)
        # ───────────────────────────────────────────────────────────────────────

        self.mirrors = [urls] if isinstance(urls, str) else urls
        if fix_urls:
            self.mirrors = [utils.url_fix(x) for x in self.mirrors]
        self.url = self.mirrors.pop(0)
        self.logger.info('Using url "{}"'.format(self.url))

        fn = urllib.parse.unquote(os.path.basename(urllib.parse.urlparse(self.url).path))
        self.dest = dest or os.path.join(tempfile.gettempdir(), 'pySmartDL', fn)

        if self.dest[-1] == os.sep:
            if os.path.exists(self.dest[:-1]) and os.path.isfile(self.dest[:-1]):
                os.unlink(self.dest[:-1])
            self.dest += fn
        if os.path.isdir(self.dest):
            self.dest = os.path.join(self.dest, fn)

        self.progress_bar = progress_bar
        self.threads_count = threads
        self.timeout = timeout
        self.current_attemp = 1
        self.attemps_limit = 4
        self.minChunkFile = 1024**2*2  # 2MB
        self.filesize = 0
        self.shared_var = multiprocessing.Value(c_int, 0)
        self.thread_shared_cmds = {}
        self.status = "ready"
        self.verify_hash = False
        self._killed = False
        self._failed = False
        self._start_func_blocking = True
        self.errors = []
        self.post_threadpool_thread = None
        self.control_thread = None

        if not os.path.exists(os.path.dirname(self.dest)):
            self.logger.info('Folder "{}" does not exist. Creating...'.format(os.path.dirname(self.dest)))
            os.makedirs(os.path.dirname(self.dest))

        if not utils.is_HTTPRange_supported(self.url, timeout=self.timeout):
            self.logger.warning("Server does not support HTTPRange. threads_count is set to 1.")
            self.threads_count = 1

        if os.path.exists(self.dest):
            self.logger.warning('Destination "{}" already exists. Existing file will be removed.'.format(self.dest))

        if not os.path.exists(os.path.dirname(self.dest)):
            self.logger.warning('Directory "{}" does not exist. Creating it...'.format(os.path.dirname(self.dest)))
            os.makedirs(os.path.dirname(self.dest))

        self.logger.info("Creating a ThreadPool of {} thread(s).".format(self.threads_count))
        self.pool = utils.ManagedThreadPoolExecutor(self.threads_count)

        if verify:
            self.context = None
        else:
            self.context = ssl.create_default_context()
            self.context.check_hostname = False
            self.context.verify_mode = ssl.CERT_NONE

    # ── Private proxy helpers ──────────────────────────────────────────────────

    def _apply_proxy(self, proxies):
        """
        Install a urllib opener that routes traffic through the given proxy.

        Accepts the same dict format used by the ``requests`` library::

            {'http': 'http://host:port', 'https': 'http://host:port'}
            {'http': 'socks5://user:pass@host:port', 'https': 'socks5://...'}

        SOCKS support requires the ``PySocks`` package (``pip install PySocks``).
        """
        handlers = []

        # Separate SOCKS entries from plain HTTP/HTTPS proxies
        http_proxy  = proxies.get('http')
        https_proxy = proxies.get('https')

        socks_proxy = http_proxy or https_proxy
        is_socks = socks_proxy and socks_proxy.lower().startswith('socks')

        if is_socks:
            handlers.append(self._build_socks_handler(proxies))
        else:
            # Standard HTTP/HTTPS proxy via urllib ProxyHandler
            # urllib expects the scheme prefix, so pass the dict as-is.
            handlers.append(urllib.request.ProxyHandler(proxies))

            # If the proxy needs Basic authentication extract credentials
            proxy_url = https_proxy or http_proxy
            if proxy_url:
                auth_handler = self._build_proxy_auth_handler(proxy_url)
                if auth_handler:
                    handlers.append(auth_handler)

        opener = urllib.request.build_opener(*handlers)
        urllib.request.install_opener(opener)

        proxy_display = https_proxy or http_proxy
        self.logger.info('Proxy configured: {}'.format(proxy_display))

    @staticmethod
    def _build_proxy_auth_handler(proxy_url):
        """
        Extract credentials from a proxy URL such as
        ``http://user:pass@host:port`` and return a
        ``ProxyBasicAuthHandler``, or ``None`` if there are no credentials.
        """
        parsed = urllib.parse.urlparse(proxy_url)
        if parsed.username and parsed.password:
            password_mgr = urllib.request.HTTPPasswordMgrWithDefaultRealm()
            proxy_host = "{}:{}".format(parsed.hostname, parsed.port) if parsed.port else parsed.hostname
            password_mgr.add_password(None, proxy_host, parsed.username, parsed.password)
            return urllib.request.ProxyBasicAuthHandler(password_mgr)
        return None

    @staticmethod
    def _build_socks_handler(proxies):
        """
        Build a urllib handler that tunnels connections through a SOCKS proxy.
        Requires the ``PySocks`` package.
        """
        try:
            import socks
            import sockshandler
            HAS_PYSOCKS = True
        except ImportError:
            HAS_PYSOCKS = False

        if not HAS_PYSOCKS:
            raise ImportError(
                "SOCKS proxy support requires PySocks. "
                "Install it with:  pip install PySocks"
            )

        proxy_url = proxies.get('https') or proxies.get('http')
        parsed = urllib.parse.urlparse(proxy_url)

        scheme = parsed.scheme.lower()
        if scheme == 'socks5':
            socks_type = socks.SOCKS5
        elif scheme == 'socks4':
            socks_type = socks.SOCKS4
        else:
            socks_type = socks.SOCKS5

        return sockshandler.SocksiPyHandler(
            socks_type,
            parsed.hostname,
            parsed.port or 1080,
            True,
            parsed.username,
            parsed.password,
        )

    # ── Public proxy helper ────────────────────────────────────────────────────

    def set_proxy(self, proxies):
        """
        Set or update the proxy after the object has been created.

        :param proxies: Proxy dictionary, same format as the constructor parameter.
                        Pass ``None`` or ``{}`` to disable the proxy.
        :type proxies: dict or None
        """
        self.proxies = proxies
        if proxies:
            self._apply_proxy(proxies)
        else:
            # Remove proxy – restore default opener (no proxy)
            opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
            urllib.request.install_opener(opener)
            self.logger.info('Proxy disabled.')

    # ──────────────────────────────────────────────────────────────────────────

    def __str__(self):
        return 'SmartDL(r"{}", dest=r"{}")'.format(self.url, self.dest)

    def __repr__(self):
        return "<SmartDL {}>".format(self.url)

    def add_basic_authentication(self, username, password):
        '''
        Uses HTTP Basic Access authentication for the connection.

        :param username: Username.
        :type username: string

        :param password: Password.
        :type password: string
        '''
        auth_string = '{}:{}'.format(username, password)
        base64string = base64.standard_b64encode(auth_string.encode('utf-8'))
        self.requestArgs['headers']['Authorization'] = b"Basic " + base64string

    def add_hash_verification(self, algorithm, hash):
        '''
        Adds hash verification to the download.

        :param algorithm: Hashing algorithm.
        :type algorithm: string

        :param hash: Hash code.
        :type hash: string
        '''
        self.verify_hash = True
        self.hash_algorithm = algorithm
        self.hash_code = hash

    def fetch_hash_sums(self):
        '''
        Will attempt to fetch UNIX hash sums files (`SHA256SUMS`, `SHA1SUMS` or `MD5SUMS` files in
        the same url directory).
        '''
        default_sums_filenames = ['SHA256SUMS', 'SHA1SUMS', 'MD5SUMS']
        folder = os.path.dirname(self.url)
        orig_basename = os.path.basename(self.url)

        self.logger.info("Looking for SUMS files...")
        for filename in default_sums_filenames:
            try:
                sums_url = "%s/%s" % (folder, filename)
                sumsRequest = urllib.request.Request(sums_url, **self.requestArgs)
                obj = urllib.request.urlopen(sumsRequest)
                data = obj.read().split('\n')
                obj.close()
                for line in data:
                    if orig_basename.lower() in line.lower():
                        self.logger.info("Found a matching hash in %s" % sums_url)
                        algo = filename.rstrip('SUMS')
                        hash = line.split(' ')[0]
                        self.add_hash_verification(algo, hash)
                        return
            except urllib.error.HTTPError:
                continue

    def start(self, blocking=None):
        '''
        Starts the download task.
        '''
        if not self.status == "ready":
            raise RuntimeError("cannot start (current status is {})".format(self.status))

        self.logger.info('Starting a new SmartDL operation.')

        if blocking is None:
            blocking = self._start_func_blocking
        else:
            self._start_func_blocking = blocking

        if self.mirrors:
            self.logger.info('One URL and {} mirrors are loaded.'.format(len(self.mirrors)))
        else:
            self.logger.info('One URL is loaded.')

        if self.verify_hash and os.path.exists(self.dest):
            if utils.get_file_hash(self.hash_algorithm, self.dest) == self.hash_code:
                self.logger.info("Destination '%s' already exists, and the hash matches. No need to download." % self.dest)
                self.status = 'finished'
                return

        self.logger.info("Downloading '{}' to '{}'...".format(self.url, self.dest))
        req = urllib.request.Request(self.url, **self.requestArgs)

        try:
            urlObj = urllib.request.urlopen(req, timeout=self.timeout, context=self.context)
        except (urllib.error.HTTPError, urllib.error.URLError, socket.timeout) as e:
            self.errors.append(e)
            if self.mirrors:
                self.logger.info("{} Trying next mirror...".format(str(e)))
                self.url = self.mirrors.pop(0)
                self.logger.info('Using url "{}"'.format(self.url))
                self.start(blocking)
                return
            else:
                self.logger.warning(str(e))
                self.errors.append(e)
                self._failed = True
                self.status = "finished"
                raise

        try:
            self.filesize = int(urlObj.headers["Content-Length"])
            self.logger.info("Content-Length is {} ({}).".format(self.filesize, utils.sizeof_human(self.filesize)))
        except (IndexError, KeyError, TypeError):
            self.logger.warning("Server did not send Content-Length. Filesize is unknown.")
            self.filesize = 0

        args = utils.calc_chunk_size(self.filesize, self.threads_count, self.minChunkFile)
        bytes_per_thread = args[0][1] - args[0][0] + 1
        if len(args) > 1:
            self.logger.info("Launching {} threads (downloads {}/thread).".format(len(args), utils.sizeof_human(bytes_per_thread)))
        else:
            self.logger.info("Launching 1 thread (downloads {}).".format(utils.sizeof_human(bytes_per_thread)))

        self.status = "downloading"

        for i, arg in enumerate(args):
            req = self.pool.submit(
                download,
                self.url,
                self.dest+".%.3d" % i,
                self.requestArgs,
                self.context,
                arg[0],
                arg[1],
                self.timeout,
                self.shared_var,
                self.thread_shared_cmds,
                self.logger
            )

        self.post_threadpool_thread = threading.Thread(
            target=post_threadpool_actions,
            args=(
                self.pool,
                [[(self.dest+".%.3d" % i) for i in range(len(args))], self.dest],
                self.filesize,
                self
            )
        )
        self.post_threadpool_thread.daemon = True
        self.post_threadpool_thread.start()

        self.control_thread = ControlThread(self)

        if blocking:
            self.wait(raise_exceptions=True)

    def _exc_callback(self, req, e):
        self.errors.append(e[0])
        self.logger.exception(e[1])

    def retry(self, eStr=""):
        if self.current_attemp < self.attemps_limit:
            self.current_attemp += 1
            self.status = "ready"
            self.shared_var.value = 0
            self.thread_shared_cmds = {}
            self.start()
        else:
            s = 'The maximum retry attempts reached'
            if eStr:
                s += " ({})".format(eStr)
            self.errors.append(urllib.error.HTTPError(self.url, "0", s, {}, StringIO()))
            self._failed = True

    def try_next_mirror(self, e=None):
        if self.mirrors:
            if e:
                self.errors.append(e)
            self.status = "ready"
            self.shared_var.value = 0
            self.url = self.mirrors.pop(0)
            self.logger.info('Using url "{}"'.format(self.url))
            self.start()
        else:
            self._failed = True
            self.errors.append(e)

    def get_eta(self, human=False):
        if human:
            s = utils.time_human(self.control_thread.get_eta())
            return s if s else "TBD"
        return self.control_thread.get_eta()

    def get_speed(self, human=False):
        if human:
            return "{}/s".format(utils.sizeof_human(self.control_thread.get_speed()))
        return self.control_thread.get_speed()

    def get_progress(self):
        if not self.filesize:
            return 0
        if self.control_thread.get_dl_size() <= self.filesize:
            return 1.0*self.control_thread.get_dl_size()/self.filesize
        return 1.0

    def get_progress_bar(self, length=20):
        return utils.progress_bar(self.get_progress(), length)

    def isFinished(self):
        if self.status == "ready":
            return False
        if self.status == "finished":
            return True
        return not self.post_threadpool_thread.is_alive()

    def isSuccessful(self):
        if self._killed:
            return False
        n = 0
        while self.status != 'finished':
            n += 1
            time.sleep(0.1)
            if n >= 15:
                raise RuntimeError("The download task must be finished in order to see if it's successful. (current status is {})".format(self.status))
        return not self._failed

    def get_errors(self):
        return self.errors

    def get_status(self):
        return self.status

    def wait(self, raise_exceptions=False):
        if self.status in ["ready", "finished"]:
            return
        while not self.isFinished():
            time.sleep(0.1)
        self.post_threadpool_thread.join()
        self.control_thread.join()
        if self._failed and raise_exceptions:
            raise self.errors[-1]

    def stop(self):
        if self.status == "downloading":
            self.thread_shared_cmds['stop'] = ""
            self._killed = True

    def pause(self):
        if self.status == "downloading":
            self.status = "paused"
            self.thread_shared_cmds['pause'] = ""

    def resume(self):
        self.unpause()

    def unpause(self):
        if self.status == "paused" and 'pause' in self.thread_shared_cmds:
            self.status = "downloading"
            del self.thread_shared_cmds['pause']

    def limit_speed(self, speed):
        if self.status == "downloading":
            if speed == 0:
                self.pause()
            else:
                self.unpause()
            if speed > 0:
                self.thread_shared_cmds['limit'] = speed/self.threads_count
            elif 'limit' in self.thread_shared_cmds:
                del self.thread_shared_cmds['limit']

    def get_dest(self):
        return self.dest

    def get_dl_time(self, human=False):
        if not self.control_thread:
            return 0
        if human:
            return utils.time_human(self.control_thread.get_dl_time())
        return self.control_thread.get_dl_time()

    def get_dl_size(self, human=False):
        if not self.control_thread:
            return 0
        if human:
            return utils.sizeof_human(self.control_thread.get_dl_size())
        return self.control_thread.get_dl_size()

    def get_final_filesize(self, human=False):
        if not self.control_thread:
            return 0
        if human:
            return utils.sizeof_human(self.control_thread.get_final_filesize())
        return self.control_thread.get_final_filesize()

    def get_data(self, binary=False, bytes=-1):
        if self.status != 'finished':
            raise RuntimeError("The download task must be finished in order to read the data. (current status is %s)" % self.status)
        flags = 'rb' if binary else 'r'
        with open(self.get_dest(), flags) as f:
            data = f.read(bytes) if bytes > 0 else f.read()
        return data

    def get_data_hash(self, algorithm):
        return hashlib.new(algorithm, self.get_data(binary=True)).hexdigest()

    def get_json(self):
        data = self.get_data()
        return json.loads(data)


def post_threadpool_actions(pool, args, expected_filesize, SmartDLObj):
    "Run function after thread pool is done. Run this in a thread."
    while not pool.done():
        time.sleep(0.1)

    if SmartDLObj._killed:
        return

    if pool.get_exception():
        for exc in pool.get_exceptions():
            SmartDLObj.logger.exception(exc)
        SmartDLObj.retry(str(pool.get_exception()))

    if SmartDLObj._failed:
        SmartDLObj.logger.warning("Task had errors. Exiting...")
        return

    if expected_filesize:
        threads = len(args[0])
        total_filesize = sum([os.path.getsize(x) for x in args[0]])
        diff = math.fabs(expected_filesize - total_filesize)
        if diff > 4*1024*threads:
            errMsg = 'Diff between downloaded files and expected filesizes is {}B (filesize: {}, expected_filesize: {}, {} threads).'.format(
                total_filesize, expected_filesize, diff, threads)
            SmartDLObj.logger.warning(errMsg)
            SmartDLObj.retry(errMsg)
            return

    SmartDLObj.status = "combining"
    utils.combine_files(*args)

    if SmartDLObj.verify_hash:
        dest_path = args[-1]
        hash_ = utils.get_file_hash(SmartDLObj.hash_algorithm, dest_path)
        if hash_ == SmartDLObj.hash_code:
            SmartDLObj.logger.info('Hash verification succeeded.')
        else:
            SmartDLObj.logger.warning('Hash verification failed.')
            SmartDLObj.try_next_mirror(HashFailedException(os.path.basename(dest_path), hash_, SmartDLObj.hash_code))
