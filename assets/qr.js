(function (g) {
  // 极简 QR 编码器：字节模式，EC=M，版本 1-6，掩码 0
  var VER = {
    1: { total: 26, ec: 10, blocks: 1, dblk: 16, align: [], cap: 14 },
    2: { total: 44, ec: 16, blocks: 1, dblk: 28, align: [6, 18], cap: 26 },
    3: { total: 70, ec: 26, blocks: 1, dblk: 44, align: [6, 22], cap: 42 },
    4: { total: 100, ec: 18, blocks: 2, dblk: 32, align: [6, 26], cap: 62 },
    5: { total: 134, ec: 24, blocks: 2, dblk: 43, align: [6, 30], cap: 84 },
    6: { total: 172, ec: 16, blocks: 4, dblk: 27, align: [6, 34], cap: 106 }
  };

  var EXP = new Array(512), LOG = new Array(256);
  (function () {
    var x = 1;
    for (var i = 0; i < 255; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & 0x100) x ^= 0x11d; }
    for (var j = 255; j < 512; j++) EXP[j] = EXP[j - 255];
  })();
  function mul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }

  function genPoly(n) {
    var poly = [1];
    for (var i = 0; i < n; i++) {
      var next = new Array(poly.length + 1).fill(0);
      for (var j = 0; j < poly.length; j++) {
        next[j] ^= mul(poly[j], 1);
        next[j + 1] ^= mul(poly[j], EXP[i]);
      }
      poly = next;
    }
    return poly;
  }

  function rsEncode(data, ecLen) {
    var gen = genPoly(ecLen);
    var res = new Array(ecLen).fill(0);
    for (var i = 0; i < data.length; i++) {
      var factor = data[i] ^ res[0];
      res.shift(); res.push(0);
      for (var j = 0; j < ecLen; j++) res[j] ^= mul(gen[j + 1], factor);
    }
    return res;
  }

  function utf8Bytes(str) {
    var out = [];
    for (var i = 0; i < str.length; i++) {
      var c = str.charCodeAt(i);
      if (c < 0x80) out.push(c);
      else if (c < 0x800) { out.push(0xc0 | (c >> 6), 0x80 | (c & 63)); }
      else { out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63)); }
    }
    return out;
  }

  function buildData(text, ver) {
    var bytes = utf8Bytes(text);
    var bits = [];
    function push(v, n) { for (var i = n - 1; i >= 0; i--) bits.push((v >> i) & 1); }
    push(4, 4);
    push(bytes.length, 8);
    for (var i = 0; i < bytes.length; i++) push(bytes[i], 8);
    var capBits = VER[ver].dblk * VER[ver].blocks * 8;
    var term = Math.min(4, capBits - bits.length);
    push(0, term);
    while (bits.length % 8) bits.push(0);
    var data = [];
    for (var j = 0; j < bits.length; j += 8) {
      var b = 0;
      for (var k = 0; k < 8; k++) b = (b << 1) | bits[j + k];
      data.push(b);
    }
    var pads = [0xec, 0x11], p = 0;
    while (data.length < VER[ver].dblk * VER[ver].blocks) { data.push(pads[p++ % 2]); }
    return data;
  }

  function makeMatrix(text) {
    // 容量保护：V1-V6（EC=M）最大 106 字节；超限返回 null，绝不静默生成不可解码的坏码
    if (typeof text !== "string") return null;
    var byteLen = utf8Bytes(text).length;
    if (byteLen < 1 || byteLen > VER[6].cap) return null;
    var ver = null;
    for (var v = 1; v <= 6; v++) if (VER[v].cap >= byteLen) { ver = v; break; }
    if (!ver) return null;
    var info = VER[ver], size = 17 + 4 * ver;
    var data = buildData(text, ver);
    var blocks = [], ecBlocks = [];
    for (var i = 0; i < info.blocks; i++) {
      var blk = data.slice(i * info.dblk, (i + 1) * info.dblk);
      blocks.push(blk);
      ecBlocks.push(rsEncode(blk, info.ec));
    }
    var inter = [];
    for (var c = 0; c < info.dblk; c++) for (var b2 = 0; b2 < info.blocks; b2++) inter.push(blocks[b2][c]);
    for (var c2 = 0; c2 < info.ec; c2++) for (var b3 = 0; b3 < info.blocks; b3++) inter.push(ecBlocks[b3][c2]);

    var m = [], fn = [];
    for (var r = 0; r < size; r++) { m.push(new Array(size).fill(0)); fn.push(new Array(size).fill(0)); }
    function setFn(r, c, v) { if (r >= 0 && r < size && c >= 0 && c < size) { m[r][c] = v; fn[r][c] = 1; } }

    // finder + separator
    function finder(r0, c0) {
      for (var r = -1; r <= 7; r++) for (var c = -1; c <= 7; c++) {
        var rr = r0 + r, cc = c0 + c;
        if (rr < 0 || rr >= size || cc < 0 || cc >= size) continue;
        var on = (r >= 0 && r <= 6 && (c === 0 || c === 6)) ||
                 (c >= 0 && c <= 6 && (r === 0 || r === 6)) ||
                 (r >= 2 && r <= 4 && c >= 2 && c <= 4);
        setFn(rr, cc, on ? 1 : 0);
      }
    }
    finder(0, 0); finder(0, size - 7); finder(size - 7, 0);
    // timing
    for (var t = 8; t < size - 8; t++) { setFn(6, t, t % 2 === 0 ? 1 : 0); setFn(t, 6, t % 2 === 0 ? 1 : 0); }
    // alignment
    var al = info.align;
    for (var ai = 0; ai < al.length; ai++) for (var aj = 0; aj < al.length; aj++) {
      var ar = al[ai], ac = al[aj];
      if ((ar === 6 && ac === 6) || (ar === 6 && ac === size - 7) || (ar === size - 7 && ac === 6)) continue;
      for (var dr = -2; dr <= 2; dr++) for (var dc = -2; dc <= 2; dc++) {
        var on2 = Math.max(Math.abs(dr), Math.abs(dc)) !== 1;
        setFn(ar + dr, ac + dc, on2 ? 1 : 0);
      }
    }
    // reserve format areas
    for (var i2 = 0; i2 < 9; i2++) { if (!fn[8][i2]) setFn(8, i2, 0); if (!fn[i2][8]) setFn(i2, 8, 0); }
    for (var i3 = 0; i3 < 8; i3++) { setFn(8, size - 1 - i3, 0); setFn(size - 1 - i3, 8, 0); }
    setFn(size - 8, 8, 1); // dark module

    // data placement
    var bitIdx = 0, totalBits = inter.length * 8;
    function nextBit() { if (bitIdx >= totalBits) return 0; var b = (inter[bitIdx >> 3] >> (7 - (bitIdx & 7))) & 1; bitIdx++; return b; }
    var col = size - 1, up = true;
    while (col > 0) {
      if (col === 6) col--;
      for (var row = 0; row < size; row++) {
        var rr2 = up ? size - 1 - row : row;
        for (var k2 = 0; k2 < 2; k2++) {
          var cc2 = col - k2;
          if (fn[rr2][cc2]) continue;
          m[rr2][cc2] = nextBit();
        }
      }
      up = !up; col -= 2;
    }
    // mask 0
    for (var r3 = 0; r3 < size; r3++) for (var c3 = 0; c3 < size; c3++)
      if (!fn[r3][c3] && (r3 + c3) % 2 === 0) m[r3][c3] ^= 1;

    // format info (EC=M=00, mask=0)
    var fmtData = (0 << 3) | 0;
    var fmt = fmtData << 10;
    for (var f = 14; f >= 10; f--) if ((fmt >> f) & 1) fmt ^= 0x537 << (f - 10);
    fmt = ((fmtData << 10) | fmt) ^ 0x5412;
    var fmtBits = [];
    for (var fb = 14; fb >= 0; fb--) fmtBits.push((fmt >> fb) & 1);
    var pos1 = [[8, 0], [8, 1], [8, 2], [8, 3], [8, 4], [8, 5], [8, 7], [8, 8], [7, 8], [5, 8], [4, 8], [3, 8], [2, 8], [1, 8], [0, 8]];
    var pos2 = [[size - 1, 8], [size - 2, 8], [size - 3, 8], [size - 4, 8], [size - 5, 8], [size - 6, 8], [size - 7, 8],
                [8, size - 8], [8, size - 7], [8, size - 6], [8, size - 5], [8, size - 4], [8, size - 3], [8, size - 2], [8, size - 1]];
    for (var p1 = 0; p1 < 15; p1++) { m[pos1[p1][0]][pos1[p1][1]] = fmtBits[p1]; m[pos2[p1][0]][pos2[p1][1]] = fmtBits[p1]; }

    return { size: size, m: m, version: ver };
  }

  g.qrMatrix = makeMatrix;
  g.qrCapacity = VER[6].cap; // 106，供调用方做容量预判
})(window);
