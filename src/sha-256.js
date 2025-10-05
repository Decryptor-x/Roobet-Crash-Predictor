/*
 * [js-sha256]{@link github.com/decryptor-x/Roobet-Crash-Predictor}
 *
 * @version 1.1.0
 * @author Decryptor
 * @copyright Decryptor 2016-2025
 * @license MIT
 */

  var SCRATCH = [];

  // robust array/view detection
  var isNativeArray = Array.isArray;
  if (ENV_ROOT.JS_SHA1_NO_NODE_JS || !isNativeArray) {
    isNativeArray = function (x) { return Object.prototype.toString.call(x) === '[object Array]'; };
  }

  var isArrayView = ArrayBuffer.isView;
  if (HAS_ARRAY_BUFFER && (ENV_ROOT.JS_SHA1_NO_ARRAY_BUFFER_IS_VIEW || !isArrayView)) {
    isArrayView = function (x) { return typeof x === 'object' && x.buffer && x.buffer.constructor === ArrayBuffer; };
  }

  // normalize input -> [value, wasString]
  function norm(v) {
    var tp = typeof v;
    if (tp === 'string') return [v, true];
    if (tp !== 'object' || v === null) throw new Error(ERROR_INVALID);
    if (HAS_ARRAY_BUFFER && v.constructor === ArrayBuffer) return [new Uint8Array(v), false];
    if (!isNativeArray(v) && !isArrayView(v)) throw new Error(ERROR_INVALID);
    return [v, false];
  }

  // create output functions that instantiate a core and return requested format
  function makeOutput(kind) {
    return function (data) {
      return new Core(true).update(data)[kind]();
    };
  }

  // top-level factory
  function buildFactory() {
    var api = makeOutput('hex');
    if (IS_NODE) api = nodeFastPath(api);

    api.create = function () { return new Core(); };
    api.update = function (m) { return api.create().update(m); };

    for (var i = 0; i < FORMATS.length; ++i) {
      api[FORMATS[i]] = makeOutput(FORMATS[i]);
    }
    return api;
  }

  // Node optimized path for hex via crypto
  function nodeFastPath(baseHex) {
    var crypto = require('crypto');
    var BufferCtor = require('buffer').Buffer;
    var bufferFrom = BufferCtor.from && !ENV_ROOT.JS_SHA1_NO_BUFFER_FROM ? BufferCtor.from : function (x) { return new BufferCtor(x); };

    return function (msg) {
      if (typeof msg === 'string') return crypto.createHash('sha1').update(msg, 'utf8').digest('hex');
      if (msg === null || msg === undefined) throw new Error(ERROR_INVALID);
      if (msg.constructor === ArrayBuffer) msg = new Uint8Array(msg);
      if (isNativeArray(msg) || isArrayView(msg) || msg.constructor === BufferCtor) {
        return crypto.createHash('sha1').update(bufferFrom(msg)).digest('hex');
      }
      return baseHex(msg);
    };
  }

  // HMAC output generator
  function makeHmac(kind) {
    return function (key, data) {
      return new Hmac(key, true).update(data)[kind]();
    };
  }

  function makeHmacFactory() {
    var h = makeHmac('hex');
    h.create = function (k) { return new Hmac(k); };
    h.update = function (k, d) { return h.create(k).update(d); };
    for (var j = 0; j < FORMATS.length; ++j) {
      (function (t) { h[t] = makeHmac(t); })(FORMATS[j]);
    }
    return h;
  }

  // --- Core SHA-1 implementation ---
  function Core(useShared) {
    if (useShared) {
      // initialize scratch (16 words + slot)
      SCRATCH[0] = SCRATCH[16] = SCRATCH[1] = SCRATCH[2] =
      SCRATCH[3] = SCRATCH[4] = SCRATCH[5] = SCRATCH[6] =
      SCRATCH[7] = SCRATCH[8] = SCRATCH[9] = SCRATCH[10] =
      SCRATCH[11] = SCRATCH[12] = SCRATCH[13] = SCRATCH[14] =
      SCRATCH[15] = 0;
      this._w = SCRATCH;
    } else {
      this._w = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    }

    // initial constants
    this._a = 0x67452301;
    this._b = 0xEFCDAB89;
    this._c = 0x98BADCFE;
    this._d = 0x10325476;
    this._e = 0xC3D2E1F0;

    this.block = this.start = this.bytes = this.hiBytes = 0;
    this.finalized = this.hashed = false;
    this.first = true;
  }

  Core.prototype.update = function (msg) {
    if (this.finalized) throw new Error(ERROR_FINALIZED);

    var pair = norm(msg);
    msg = pair[0];
    var isStr = pair[1];

    var code = 0, pos = 0, i, len = msg.length || 0, w = this._w;

    while (pos < len) {
      if (this.hashed) {
        this.hashed = false;
        w[0] = this.block;
        this.block = w[16] = w[1] = w[2] = w[3] =
        w[4] = w[5] = w[6] = w[7] =
        w[8] = w[9] = w[10] = w[11] =
        w[12] = w[13] = w[14] = w[15] = 0;
      }

      if (isStr) {
        for (i = this.start; pos < len && i < 64; ++pos) {
          code = msg.charCodeAt(pos);
          if (code < 0x80) {
            w[i >>> 2] |= code << SHIFT_LOOKUP[i++ & 3];
          } else if (code < 0x800) {
            w[i >>> 2] |= (0xc0 | (code >>> 6)) << SHIFT_LOOKUP[i++ & 3];
            w[i >>> 2] |= (0x80 | (code & 0x3f)) << SHIFT_LOOKUP[i++ & 3];
          } else if (code < 0xD800 || code >= 0xE000) {
            w[i >>> 2] |= (0xe0 | (code >>> 12)) << SHIFT_LOOKUP[i++ & 3];
            w[i >>> 2] |= (0x80 | ((code >>> 6) & 0x3f)) << SHIFT_LOOKUP[i++ & 3];
            w[i >>> 2] |= (0x80 | (code & 0x3f)) << SHIFT_LOOKUP[i++ & 3];
          } else {
            // surrogate pair
            code = 0x10000 + (((code & 0x3ff) << 10) | (msg.charCodeAt(++pos) & 0x3ff));
            w[i >>> 2] |= (0xf0 | (code >>> 18)) << SHIFT_LOOKUP[i++ & 3];
            w[i >>> 2] |= (0x80 | ((code >>> 12) & 0x3f)) << SHIFT_LOOKUP[i++ & 3];
            w[i >>> 2] |= (0x80 | ((code >>> 6) & 0x3f)) << SHIFT_LOOKUP[i++ & 3];
            w[i >>> 2] |= (0x80 | (code & 0x3f)) << SHIFT_LOOKUP[i++ & 3];
          }
        }
      } else {
        for (i = this.start; pos < len && i < 64; ++pos) {
          w[i >>> 2] |= msg[pos] << SHIFT_LOOKUP[i++ & 3];
        }
      }

      this.lastByteIndex = i;
      this.bytes += i - this.start;

      if (i >= 64) {
        this.block = w[16];
        this.start = i - 64;
        this._compress();
        this.hashed = true;
      } else {
        this.start = i;
      }
    }

    if (this.bytes > 0xFFFFFFFF) {
      this.hiBytes += (this.bytes / 4294967296) | 0;
      this.bytes = this.bytes % 4294967296;
    }
    return this;
  };

  Core.prototype.finalize = function () {
    if (this.finalized) return;
    this.finalized = true;

    var w = this._w, j = this.lastByteIndex;
    w[16] = this.block;
    w[j >>> 2] |= PAD_LOOKUP[j & 3];
    this.block = w[16];

    if (j >= 56) {
      if (!this.hashed) this._compress();
      w[0] = this.block;
      w[16] = w[1] = w[2] = w[3] =
      w[4] = w[5] = w[6] = w[7] =
      w[8] = w[9] = w[10] = w[11] =
      w[12] = w[13] = w[14] = w[15] = 0;
    }

    w[14] = (this.hiBytes << 3) | (this.bytes >>> 29);
    w[15] = this.bytes << 3;
    this._compress();
  };

  // compression function (algorithm preserved)
  Core.prototype._compress = function () {
    var a = this._a, b = this._b, c = this._c, d = this._d, e = this._e;
    var w = this._w, t;

    for (var i = 16; i < 80; ++i) {
      t = w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16];
      w[i] = (t << 1) | (t >>> 31);
    }

    var s = 0;
    for (; s < 20; s += 5) {
      var f = (b & c) | ((~b) & d);
      t = ((a << 5) | (a >>> 27)) + f + e + 1518500249 + (w[s] << 0);
      e = (t << 0) | 0;
      b = (b << 30) | (b >>> 2);

      f = (a & b) | ((~a) & c);
      t = ((e << 5) | (e >>> 27)) + f + d + 1518500249 + (w[s + 1] << 0);
      d = (t << 0) | 0;
      a = (a << 30) | (a >>> 2);

      f = (e & a) | ((~e) & b);
      t = ((d << 5) | (d >>> 27)) + f + c + 1518500249 + (w[s + 2] << 0);
      c = (t << 0) | 0;
      e = (e << 30) | (e >>> 2);

      f = (d & e) | ((~d) & a);
      t = ((c << 5) | (c >>> 27)) + f + b + 1518500249 + (w[s + 3] << 0);
      b = (t << 0) | 0;
      d = (d << 30) | (d >>> 2);

      f = (c & b) | ((~c) & e);
      t = ((b << 5) | (b >>> 27)) + f + a + 1518500249 + (w[s + 4] << 0);
      a = (t << 0) | 0;
      c = (c << 30) | (c >>> 2);
    }

    for (; s < 40; s += 5) {
      var ff = b ^ c ^ d;
      t = ((a << 5) | (a >>> 27)) + ff + e + 1859775393 + (w[s] << 0);
      e = (t << 0) | 0;
      b = (b << 30) | (b >>> 2);

      ff = a ^ b ^ c;
      t = ((e << 5) | (e >>> 27)) + ff + d + 1859775393 + (w[s + 1] << 0);
      d = (t << 0) | 0;
      a = (a << 30) | (a >>> 2);

      ff = e ^ a ^ b;
      t = ((d << 5) | (d >>> 27)) + ff + c + 1859775393 + (w[s + 2] << 0);
      c = (t << 0) | 0;
      e = (e << 30) | (e >>> 2);

      ff = d ^ e ^ a;
      t = ((c << 5) | (c >>> 27)) + ff + b + 1859775393 + (w[s + 3] << 0);
      b = (t << 0) | 0;
      d = (d << 30) | (d >>> 2);

      ff = c ^ b ^ e;
      t = ((b << 5) | (b >>> 27)) + ff + a + 1859775393 + (w[s + 4] << 0);
      a = (t << 0) | 0;
      c = (c << 30) | (c >>> 2);
    }

    for (; s < 60; s += 5) {
      var fff = (b & c) | (b & d) | (c & d);
      t = ((a << 5) | (a >>> 27)) + fff + e - 1894007588 + (w[s] << 0);
      e = (t << 0) | 0;
      b = (b << 30) | (b >>> 2);

      fff = (a & b) | (a & c) | (b & c);
      t = ((e << 5) | (e >>> 27)) + fff + d - 1894007588 + (w[s + 1] << 0);
      d = (t << 0) | 0;
      a = (a << 30) | (a >>> 2);

      fff = (e & a) | (e & b) | (a & b);
      t = ((d << 5) | (d >>> 27)) + fff + c - 1894007588 + (w[s + 2] << 0);
      c = (t << 0) | 0;
      e = (e << 30) | (e >>> 2);

      fff = (d & e) | (d & a) | (e & a);
      t = ((c << 5) | (c >>> 27)) + fff + b - 1894007588 + (w[s + 3] << 0);
      b = (t << 0) | 0;
      d = (d << 30) | (d >>> 2);

      fff = (c & b) | (c & e) | (b & e);
      t = ((b << 5) | (b >>> 27)) + fff + a - 1894007588 + (w[s + 4] << 0);
      a = (t << 0) | 0;
      c = (c << 30) | (c >>> 2);
    }

    for (; s < 80; s += 5) {
      var f4 = b ^ c ^ d;
      t = ((a << 5) | (a >>> 27)) + f4 + e - 899497514 + (w[s] << 0);
      e = (t << 0) | 0;
      b = (b << 30) | (b >>> 2);

      f4 = a ^ b ^ c;
      t = ((e << 5) | (e >>> 27)) + f4 + d - 899497514 + (w[s + 1] << 0);
      d = (t << 0) | 0;
      a = (a << 30) | (a >>> 2);

      f4 = e ^ a ^ b;
      t = ((d << 5) | (d >>> 27)) + f4 + c - 899497514 + (w[s + 2] << 0);
      c = (t << 0) | 0;
      e = (e << 30) | (e >>> 2);

      f4 = d ^ e ^ a;
      t = ((c << 5) | (c >>> 27)) + f4 + b - 899497514 + (w[s + 3] << 0);
      b = (t << 0) | 0;
      d = (d << 30) | (d >>> 2);

      f4 = c ^ b ^ e;
      t = ((b << 5) | (b >>> 27)) + f4 + a - 899497514 + (w[s + 4] << 0);
      a = (t << 0) | 0;
      c = (c << 30) | (c >>> 2);
    }

    this._a = (this._a + a) << 0;
    this._b = (this._b + b) << 0;
    this._c = (this._c + c) << 0;
    this._d = (this._d + d) << 0;
    this._e = (this._e + e) << 0;
  };

  // hex output
  Core.prototype.hex = function () {
    this.finalize();
    var a = this._a, b = this._b, c = this._c, d = this._d, e = this._e;
    return HEX_CHARS[(a >>> 28) & 0x0F] + HEX_CHARS[(a >>> 24) & 0x0F] +
           HEX_CHARS[(a >>> 20) & 0x0F] + HEX_CHARS[(a >>> 16) & 0x0F] +
           HEX_CHARS[(a >>> 12) & 0x0F] + HEX_CHARS[(a >>> 8) & 0x0F] +
           HEX_CHARS[(a >>> 4) & 0x0F] + HEX_CHARS[a & 0x0F] +
           HEX_CHARS[(b >>> 28) & 0x0F] + HEX_CHARS[(b >>> 24) & 0x0F] +
           HEX_CHARS[(b >>> 20) & 0x0F] + HEX_CHARS[(b >>> 16) & 0x0F] +
           HEX_CHARS[(b >>> 12) & 0x0F] + HEX_CHARS[(b >>> 8) & 0x0F] +
           HEX_CHARS[(b >>> 4) & 0x0F] + HEX_CHARS[b & 0x0F] +
           HEX_CHARS[(c >>> 28) & 0x0F] + HEX_CHARS[(c >>> 24) & 0x0F] +
           HEX_CHARS[(c >>> 20) & 0x0F] + HEX_CHARS[(c >>> 16) & 0x0F] +
           HEX_CHARS[(c >>> 12) & 0x0F] + HEX_CHARS[(c >>> 8) & 0x0F] +
           HEX_CHARS[(c >>> 4) & 0x0F] + HEX_CHARS[c & 0x0F] +
           HEX_CHARS[(d >>> 28) & 0x0F] + HEX_CHARS[(d >>> 24) & 0x0F] +
           HEX_CHARS[(d >>> 20) & 0x0F] + HEX_CHARS[(d >>> 16) & 0x0F] +
           HEX_CHARS[(d >>> 12) & 0x0F] + HEX_CHARS[(d >>> 8) & 0x0F] +
           HEX_CHARS[(d >>> 4) & 0x0F] + HEX_CHARS[d & 0x0F] +
           HEX_CHARS[(e >>> 28) & 0x0F] + HEX_CHARS[(e >>> 24) & 0x0F] +
           HEX_CHARS[(e >>> 20) & 0x0F] + HEX_CHARS[(e >>> 16) & 0x0F] +
           HEX_CHARS[(e >>> 12) & 0x0F] + HEX_CHARS[(e >>> 8) & 0x0F] +
           HEX_CHARS[(e >>> 4) & 0x0F] + HEX_CHARS[e & 0x0F];
  };

  Core.prototype.toString = Core.prototype.hex;

  // digest (raw bytes)
  Core.prototype.digest = function () {
    this.finalize();
    var a = this._a, b = this._b, c = this._c, d = this._d, e = this._e;
    return [
      (a >>> 24) & 0xFF, (a >>> 16) & 0xFF, (a >>> 8) & 0xFF, a & 0xFF,
      (b >>> 24) & 0xFF, (b >>> 16) & 0xFF, (b >>> 8) & 0xFF, b & 0xFF,
      (c >>> 24) & 0xFF, (c >>> 16) & 0xFF, (c >>> 8) & 0xFF, c & 0xFF,
      (d >>> 24) & 0xFF, (d >>> 16) & 0xFF, (d >>> 8) & 0xFF, d & 0xFF,
      (e >>> 24) & 0xFF, (e >>> 16) & 0xFF, (e >>> 8) & 0xFF, e & 0xFF
    ];
  };

  Core.prototype.array = Core.prototype.digest;

  Core.prototype.arrayBuffer = function () {
    this.finalize();
    var b = new ArrayBuffer(20);
    var dv = new DataView(b);
    dv.setUint32(0, this._a);
    dv.setUint32(4, this._b);
    dv.setUint32(8, this._c);
    dv.setUint32(12, this._d);
    dv.setUint32(16, this._e);
    return b;
  };

  // --- HMAC wrapper ---
  function Hmac(key, useShared) {
    var p = norm(key);
    key = p[0];

    if (p[1]) {
      var bytes = [], q = 0, ch;
      for (var r = 0, L = key.length; r < L; ++r) {
        ch = key.charCodeAt(r);
        if (ch < 0x80) {
          bytes[q++] = ch;
        } else if (ch < 0x800) {
          bytes[q++] = 0xc0 | (ch >>> 6);
          bytes[q++] = 0x80 | (ch & 0x3f);
        } else if (ch < 0xD800 || ch >= 0xE000) {
          bytes[q++] = 0xe0 | (ch >>> 12);
          bytes[q++] = 0x80 | ((ch >>> 6) & 0x3f);
          bytes[q++] = 0x80 | (ch & 0x3f);
        } else {
          ch = 0x10000 + (((ch & 0x3ff) << 10) | (key.charCodeAt(++r) & 0x3ff));
          bytes[q++] = 0xf0 | (ch >>> 18);
          bytes[q++] = 0x80 | ((ch >>> 12) & 0x3f);
          bytes[q++] = 0x80 | ((ch >>> 6) & 0x3f);
          bytes[q++] = 0x80 | (ch & 0x3f);
        }
      }
      key = bytes;
    }

    if (key.length > 64) key = (new Core(true)).update(key).array();

    var oPad = [], iPad = [];
    for (i = 0; i < 64; ++i) {
      var kb = key[i] || 0;
      oPad[i] = 0x5c ^ kb;
      iPad[i] = 0x36 ^ kb;
    }

    Core.call(this, useShared);
    this.update(iPad);
    this._o = oPad;
    this._inner = true;
    this._sharedFlag = useShared;
  }
  Hmac.prototype = new Core();

  Hmac.prototype.finalize = function () {
    Core.prototype.finalize.call(this);
    if (this._inner) {
      this._inner = false;
      var inner = this.array();
      Core.call(this, this._sharedFlag);
      this.update(this._o);
      this.update(inner);
      Core.prototype.finalize.call(this);
    }
  };

  // --- Public wiring ---
  var sha1 = buildFactory();
  sha1.sha1 = sha1;
  sha1.sha1.hmac = makeHmacFactory();

  if (IS_COMMONJS) {
    module.exports = sha1;
  } else {
    ENV_ROOT.sha1 = sha1;
    if (IS_AMD) define(function () { return sha1; });
  }

}());