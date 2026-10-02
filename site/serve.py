#!/usr/bin/env python3
"""Serve the site at http://localhost:8000 with caching disabled: python3 site/serve.py"""

import functools
import http.server
import os


class NoCache(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()


handler = functools.partial(NoCache, directory=os.path.dirname(os.path.abspath(__file__)))
http.server.ThreadingHTTPServer(("", 8000), handler).serve_forever()
