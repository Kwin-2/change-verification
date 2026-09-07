/* ============================================================
 * jscrypto.js — 纯 JS 加密兜底模块（无第三方依赖）
 * 用于内网 plain HTTP 等无 WebCrypto（crypto.subtle）的环境：
 *   - SHA-256 / HMAC-SHA256 / PBKDF2-SHA256
 *   - AES-256-GCM 解密（CTR + GHASH，含 tag 校验）
 * 仅在 crypto.subtle 不可用时由 app.js 调用；有 WebCrypto 时不参与。
 * ============================================================ */
(function (global) {
'use strict';

/* ---------- SHA-256 ---------- */
var K256 = new Uint32Array([
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
]);

function rotr(x, n) { return (x >>> n) | (x << (32 - n)); }

/* 对 64 字节分组做压缩；h 为 8 个 Uint32 状态（原地更新） */
function sha256Compress(h, block, offset) {
  var w = new Uint32Array(64);
  var i, t;
  for (i = 0; i < 16; i++) {
    var j = offset + i * 4;
    w[i] = (block[j] << 24) | (block[j+1] << 16) | (block[j+2] << 8) | block[j+3];
  }
  for (i = 16; i < 64; i++) {
    var s0 = rotr(w[i-15], 7) ^ rotr(w[i-15], 18) ^ (w[i-15] >>> 3);
    var s1 = rotr(w[i-2], 17) ^ rotr(w[i-2], 19) ^ (w[i-2] >>> 10);
    w[i] = (w[i-16] + s0 + w[i-7] + s1) | 0;
  }
  var a=h[0],b=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
  for (t = 0; t < 64; t++) {
    var S1 = rotr(e,6) ^ rotr(e,11) ^ rotr(e,25);
    var ch = (e & f) ^ (~e & g);
    var t1 = (hh + S1 + ch + K256[t] + w[t]) | 0;
    var S0 = rotr(a,2) ^ rotr(a,13) ^ rotr(a,22);
    var maj = (a & b) ^ (a & c) ^ (b & c);
    var t2 = (S0 + maj) | 0;
    hh=g; g=f; f=e; e=(d+t1)|0; d=c; c=b; b=a; a=(t1+t2)|0;
  }
  h[0]=(h[0]+a)|0; h[1]=(h[1]+b)|0; h[2]=(h[2]+c)|0; h[3]=(h[3]+d)|0;
  h[4]=(h[4]+e)|0; h[5]=(h[5]+f)|0; h[6]=(h[6]+g)|0; h[7]=(h[7]+hh)|0;
}

function sha256Init() {
  return new Uint32Array([0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19]);
}

/* 一次性 SHA-256，输入 Uint8Array，输出 Uint8Array(32) */
function sha256(data) {
  var h = sha256Init();
  var len = data.length;
  var full = len - (len % 64);
  var i;
  for (i = 0; i < full; i += 64) sha256Compress(h, data, i);
  /* padding */
  var tail = new Uint8Array(128);
  var rem = len - full;
  tail.set(data.subarray(full, full + rem));
  tail[rem] = 0x80;
  var tailLen = (rem >= 56) ? 128 : 64;
  var bitLenHi = Math.floor(len / 0x20000000);
  var bitLenLo = (len << 3) >>> 0;
  tail[tailLen-8] = (bitLenHi >>> 24) & 0xff; tail[tailLen-7] = (bitLenHi >>> 16) & 0xff;
  tail[tailLen-6] = (bitLenHi >>> 8) & 0xff;  tail[tailLen-5] = bitLenHi & 0xff;
  tail[tailLen-4] = (bitLenLo >>> 24) & 0xff; tail[tailLen-3] = (bitLenLo >>> 16) & 0xff;
  tail[tailLen-2] = (bitLenLo >>> 8) & 0xff;  tail[tailLen-1] = bitLenLo & 0xff;
  sha256Compress(h, tail, 0);
  if (tailLen === 128) sha256Compress(h, tail, 64);
  var out = new Uint8Array(32);
  for (i = 0; i < 8; i++) {
    out[i*4]   = (h[i] >>> 24) & 0xff;
    out[i*4+1] = (h[i] >>> 16) & 0xff;
    out[i*4+2] = (h[i] >>> 8) & 0xff;
    out[i*4+3] = h[i] & 0xff;
  }
  return out;
}

/* ---------- HMAC-SHA256（key 已预处理为 64 字节 ipad/opad 状态） ---------- */
function hmacStates(keyBytes) {
  var k = keyBytes;
  if (k.length > 64) k = sha256(k);
  var ipad = new Uint8Array(64), opad = new Uint8Array(64);
  for (var i = 0; i < 64; i++) {
    var b = i < k.length ? k[i] : 0;
    ipad[i] = b ^ 0x36;
    opad[i] = b ^ 0x5c;
  }
  /* 预计算压缩后的中间状态 */
  var hi = sha256Init(); sha256Compress(hi, ipad, 0);
  var ho = sha256Init(); sha256Compress(ho, opad, 0);
  return { hi: hi, ho: ho };
}

/* 用预处理状态计算 HMAC(msg)，msg 必须 <= 55 字节（本场景最大 36 字节，单分组） */
function hmacShort(st, msg) {
  var h1 = st.hi.slice();
  var block = new Uint8Array(128);
  block.set(msg);
  block[msg.length] = 0x80;
  var tailLen = (msg.length >= 56) ? 128 : 64;
  var totalBits = (64 + msg.length) * 8;
  block[tailLen-4] = (totalBits >>> 24) & 0xff; block[tailLen-3] = (totalBits >>> 16) & 0xff;
  block[tailLen-2] = (totalBits >>> 8) & 0xff; block[tailLen-1] = totalBits & 0xff;
  sha256Compress(h1, block, 0);
  if (tailLen === 128) sha256Compress(h1, block, 64);
  var inner = new Uint8Array(32);
  for (var i = 0; i < 8; i++) {
    inner[i*4]=(h1[i]>>>24)&0xff; inner[i*4+1]=(h1[i]>>>16)&0xff;
    inner[i*4+2]=(h1[i]>>>8)&0xff; inner[i*4+3]=h1[i]&0xff;
  }
  var h2 = st.ho.slice();
  var b2 = new Uint8Array(64);
  b2.set(inner); b2[32] = 0x80;
  var tb = (64 + 32) * 8;
  b2[60]=(tb>>>24)&0xff; b2[61]=(tb>>>16)&0xff; b2[62]=(tb>>>8)&0xff; b2[63]=tb&0xff;
  sha256Compress(h2, b2, 0);
  var out = new Uint8Array(32);
  for (i = 0; i < 8; i++) {
    out[i*4]=(h2[i]>>>24)&0xff; out[i*4+1]=(h2[i]>>>16)&0xff;
    out[i*4+2]=(h2[i]>>>8)&0xff; out[i*4+3]=h2[i]&0xff;
  }
  return out;
}

/* ---------- PBKDF2-SHA256（dkLen=32，单块；分片让出主线程） ---------- */
function pbkdf2Sha256(passwordBytes, salt, iterations, onProgress) {
  return new Promise(function (resolve) {
    var st = hmacStates(passwordBytes);
    var msg = new Uint8Array(salt.length + 4);
    msg.set(salt);
    msg[salt.length+3] = 1; /* block index = 1 */
    var u = hmacShort(st, msg);
    var t = u.slice();
    var i = 1;
    var CHUNK = 4000;
    function step() {
      var end = Math.min(i + CHUNK, iterations);
      for (; i < end; i++) {
        u = hmacShort(st, u);
        for (var j = 0; j < 32; j++) t[j] ^= u[j];
      }
      if (onProgress) onProgress(i / iterations);
      if (i < iterations) setTimeout(step, 0);
      else resolve(t);
    }
    step();
  });
}

/* ---------- AES-256 ---------- */
/* 标准 AES S 盒（直接查表，避免运行时生成出错） */
var SBOX = new Uint8Array([
  0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
  0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
  0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
  0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
  0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
  0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
  0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
  0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
  0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
  0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
  0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
  0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
  0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
  0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
  0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
  0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16
]);

function aesExpandKey(keyBytes) {
  /* AES-256: Nk=8, Nr=14 → 60 个 word */
  var w = new Uint32Array(60);
  var i;
  for (i = 0; i < 8; i++) {
    w[i] = (keyBytes[i*4] << 24) | (keyBytes[i*4+1] << 16) | (keyBytes[i*4+2] << 8) | keyBytes[i*4+3];
  }
  var RCON = [0x01000000,0x02000000,0x04000000,0x08000000,0x10000000,0x20000000,0x40000000];
  for (i = 8; i < 60; i++) {
    var t = w[i-1];
    if (i % 8 === 0) {
      t = ((SBOX[(t>>>16)&0xff]<<24)|(SBOX[(t>>>8)&0xff]<<16)|(SBOX[t&0xff]<<8)|SBOX[(t>>>24)&0xff]) ^ RCON[i/8-1];
    } else if (i % 8 === 4) {
      t = (SBOX[(t>>>24)&0xff]<<24)|(SBOX[(t>>>16)&0xff]<<16)|(SBOX[(t>>>8)&0xff]<<8)|SBOX[t&0xff];
    }
    w[i] = (w[i-8] ^ t) >>> 0;
  }
  /* 展平为每轮 16 字节 */
  var rk = [];
  for (i = 0; i < 60; i++) {
    rk.push([(w[i]>>>24)&0xff,(w[i]>>>16)&0xff,(w[i]>>>8)&0xff,w[i]&0xff]);
  }
  return rk;
}

function xtime(b) { b <<= 1; if (b & 0x100) b ^= 0x11b; return b & 0xff; }
function mul2(b){ return xtime(b); }
function mul3(b){ return xtime(b) ^ b; }

function aesEncryptBlock(rk, input) {
  /* input: Uint8Array(16)，输出 Uint8Array(16)。列主序 state[r][c] = input[c*4+r] */
  var s = new Uint8Array(16);
  var i, r, c;
  for (i = 0; i < 16; i++) s[i] = input[i] ^ rk[i >> 2][i & 3];
  for (var round = 1; round <= 14; round++) {
    /* SubBytes */
    for (i = 0; i < 16; i++) s[i] = SBOX[s[i]];
    /* ShiftRows（state[c*4+r]） */
    var t;
    /* row1: 左移1 */
    t=s[1]; s[1]=s[5]; s[5]=s[9]; s[9]=s[13]; s[13]=t;
    /* row2: 左移2 */
    t=s[2]; s[2]=s[10]; s[10]=t; t=s[6]; s[6]=s[14]; s[14]=t;
    /* row3: 左移3 = 右移1 */
    t=s[15]; s[15]=s[11]; s[11]=s[7]; s[7]=s[3]; s[3]=t;
    /* MixColumns（最后一轮跳过） */
    if (round < 14) {
      for (c = 0; c < 4; c++) {
        var a0=s[c*4], a1=s[c*4+1], a2=s[c*4+2], a3=s[c*4+3];
        s[c*4]   = mul2(a0)^mul3(a1)^a2^a3;
        s[c*4+1] = a0^mul2(a1)^mul3(a2)^a3;
        s[c*4+2] = a0^a1^mul2(a2)^mul3(a3);
        s[c*4+3] = mul3(a0)^a1^a2^mul2(a3);
      }
    }
    /* AddRoundKey */
    for (i = 0; i < 16; i++) s[i] ^= rk[round*4 + (i >> 2)][i & 3];
  }
  return s;
}

/* ---------- GHASH（GF(2^128)，无 AAD） ---------- */
function ghashInit(rk) {
  var zero = new Uint8Array(16);
  return aesEncryptBlock(rk, zero); /* H = E(K, 0^128) */
}

function gfMul(xBytes, yBytes) {
  /* 返回 x·y（GF(2^128)，多项式表示法） */
  var z = new Uint8Array(16);
  var v = yBytes.slice();
  for (var i = 0; i < 128; i++) {
    var byteIdx = i >> 3, bitIdx = 7 - (i & 7);
    if ((xBytes[byteIdx] >> bitIdx) & 1) {
      for (var j = 0; j < 16; j++) z[j] ^= v[j];
    }
    /* v = v * x（右移一位，若溢出则异或 R=0xe1<<120） */
    var lsb = v[15] & 1;
    for (j = 15; j > 0; j--) v[j] = ((v[j] >>> 1) | ((v[j-1] & 1) << 7)) & 0xff;
    v[0] = (v[0] >>> 1) & 0xff;
    if (lsb) v[0] ^= 0xe1;
  }
  return z;
}

function xorBlock(a, b) { var o = new Uint8Array(16); for (var i = 0; i < 16; i++) o[i] = a[i]^b[i]; return o; }

/* ---------- AES-256-GCM 解密 ---------- */
function aesGcmDecrypt(keyBytes, iv, data) {
  /* data = ciphertext || tag(16)。iv 为 12 字节。 */
  if (data.length < 16) throw new Error('GCM: data too short');
  var ctLen = data.length - 16;
  var ct = data.subarray(0, ctLen);
  var tag = data.subarray(ctLen);
  var rk = aesExpandKey(keyBytes);
  var H = ghashInit(rk);

  /* J0 = iv || 0x00000001（96-bit iv） */
  var J0 = new Uint8Array(16);
  J0.set(iv); J0[15] = 1;

  /* GHASH：无 AAD → 仅密文块 + 长度块 */
  var y = new Uint8Array(16);
  var i;
  for (i = 0; i < ctLen; i += 16) {
    var blk = new Uint8Array(16);
    var n = Math.min(16, ctLen - i);
    blk.set(ct.subarray(i, i + n));
    y = gfMul(xorBlock(y, blk), H);
  }
  var lenBlk = new Uint8Array(16);
  var bitLen = ctLen * 8;
  /* 高 64 位为 AAD 长度（0），低 64 位为密文长度 */
  var hi = Math.floor(bitLen / 0x100000000);
  var lo = bitLen >>> 0;
  lenBlk[8]=(hi>>>24)&0xff; lenBlk[9]=(hi>>>16)&0xff; lenBlk[10]=(hi>>>8)&0xff; lenBlk[11]=hi&0xff;
  lenBlk[12]=(lo>>>24)&0xff; lenBlk[13]=(lo>>>16)&0xff; lenBlk[14]=(lo>>>8)&0xff; lenBlk[15]=lo&0xff;
  y = gfMul(xorBlock(y, lenBlk), H);

  var s = aesEncryptBlock(rk, J0); /* E(K, J0) */
  var calcTag = xorBlock(y, s);
  var diff = 0;
  for (i = 0; i < 16; i++) diff |= calcTag[i] ^ tag[i];
  if (diff !== 0) throw new Error('GCM: tag mismatch');

  /* CTR 解密：计数器从 inc32(J0) 开始 */
  var out = new Uint8Array(ctLen);
  var counter = J0.slice();
  for (i = 0; i < ctLen; i += 16) {
    /* inc32（注意：Uint8Array 赋值自动回绕，必须先读改写再判进位） */
    var c = 15;
    while (true) {
      counter[c] = (counter[c] + 1) & 0xff;
      if (counter[c] !== 0 || c === 12) break;
      c--;
    }
    var ks = aesEncryptBlock(rk, counter);
    var n2 = Math.min(16, ctLen - i);
    for (var j = 0; j < n2; j++) out[i+j] = ct[i+j] ^ ks[j];
  }
  return out;
}

/* ---------- 对外接口 ---------- */
global.JSC = {
  sha256: sha256,
  pbkdf2Sha256: pbkdf2Sha256,
  aesGcmDecrypt: aesGcmDecrypt,
  _aesBlock: function (keyBytes, block16) { return aesEncryptBlock(aesExpandKey(keyBytes), block16); }
};
})(typeof window !== 'undefined' ? window : this);
