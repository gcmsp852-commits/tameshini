/**
 * dm.js — Data Matrix (ECC200) encoder with Management Code support
 *
 * 対応仕様:
 *  - ASCII モード（0-127 は value+1 で1バイト、128-255 は upper shift で2バイト）
 *  - Base256 モード（任意バイト列）
 *  - ECC200 Reed-Solomon 誤り訂正
 *  - 12×12 〜 144×144 の正方シンボルサイズ
 *  - 管理部32ビット・拡張管理部の挿入
 *  - XORマスク（ユーザ暗号化）対応
 *
 * qrcode.js と同等の API インターフェースを提供します:
 *  - dm.addData(text, "Byte")
 *  - dm.setManagementBits(bits32)
 *  - dm.setManagementExtBlocks([{bits, bitCount}, ...])
 *  - dm.setLocationExt48(value)
 *  - dm.setMunicipalityExt24(value)
 *  - dm.setXorMaskBytes(Uint8Array)
 *  - dm.make()
 *  - dm.getModuleCount() → セル数
 *  - dm.isDark(row, col) → bool
 *  - dm.getTotalCodeCount() → データ+ECC総コード語数
 *  - dm.getRSBlockInfo() → { dataCount, eccCount, blocks }
 */

(function(global) {
  'use strict';

  // ===== Data Matrix 符号表 (ECC200 正方シンボル) =====
  // [ size, dataCap, eccCap, blocks(interleave), dataRegionSize, mappingAreaSize ]
  // dataRegionSize: 内部分割の1データ領域のサイズ
  // mappingAreaSize: 実際に数値配置される領域サイズ (外周なし)
  const DM_SYMBOLS = [
    // size, data, ecc, blocks, regionRows, regionCols, mappingSize
    { size:10, data:3,    ecc:5,   blocks:1, regions:[1,1], mapping:8   },
    { size:12, data:5,    ecc:7,   blocks:1, regions:[1,1], mapping:10  },
    { size:14, data:8,    ecc:10,  blocks:1, regions:[1,1], mapping:12  },
    { size:16, data:12,   ecc:12,  blocks:1, regions:[1,1], mapping:14  },
    { size:18, data:18,   ecc:14,  blocks:1, regions:[1,1], mapping:16  },
    { size:20, data:22,   ecc:18,  blocks:1, regions:[1,1], mapping:18  },
    { size:22, data:30,   ecc:20,  blocks:1, regions:[1,1], mapping:20  },
    { size:24, data:36,   ecc:24,  blocks:1, regions:[1,1], mapping:22  },
    { size:26, data:44,   ecc:28,  blocks:1, regions:[1,1], mapping:24  },
    { size:32, data:62,   ecc:36,  blocks:1, regions:[2,2], mapping:28  },
    { size:36, data:86,   ecc:42,  blocks:1, regions:[2,2], mapping:32  },
    { size:40, data:114,  ecc:48,  blocks:1, regions:[2,2], mapping:36  },
    { size:44, data:144,  ecc:56,  blocks:1, regions:[2,2], mapping:40  },
    { size:48, data:174,  ecc:68,  blocks:1, regions:[2,2], mapping:44  },
    { size:52, data:204,  ecc:84,  blocks:2, regions:[2,2], mapping:48  },
    { size:64, data:280,  ecc:112, blocks:2, regions:[4,4], mapping:56  },
    { size:72, data:368,  ecc:144, blocks:4, regions:[4,4], mapping:64  },
    { size:80, data:456,  ecc:192, blocks:4, regions:[4,4], mapping:72  },
    { size:88, data:576,  ecc:224, blocks:4, regions:[4,4], mapping:80  },
    { size:96, data:696,  ecc:272, blocks:4, regions:[4,4], mapping:88  },
    { size:104,data:816,  ecc:336, blocks:6, regions:[4,4], mapping:96  },
    { size:120,data:1050, ecc:408, blocks:6, regions:[6,6], mapping:108 },
    { size:132,data:1304, ecc:496, blocks:8, regions:[6,6], mapping:120 },
    { size:144,data:1558, ecc:620, blocks:10,regions:[6,6], mapping:132 }
  ];

  function getSymbolBySize(size) {
    for (const s of DM_SYMBOLS) if (s.size === size) return s;
    throw new Error("サポートされていない Data Matrix サイズ: " + size);
  }

  // 必要データバイト数に応じた最小シンボルを返す
  function selectSymbol(totalBytes) {
    for (const s of DM_SYMBOLS) {
      if (s.data >= totalBytes) return s;
    }
    throw new Error("データが大きすぎます: " + totalBytes + " bytes");
  }

  // ===== GF(256) 演算 (Data Matrix 用 多項式 0x12D) =====
  // ECC200 primitive polynomial: x^8 + x^5 + x^3 + x^2 + 1 = 301 (0x12D)
  const DM_PRIM = 0x12D;
  const gfExp = new Uint8Array(512);
  const gfLog = new Uint8Array(256);
  (function initGF() {
    let x = 1;
    for (let i = 0; i < 255; i++) {
      gfExp[i] = x;
      gfLog[x] = i;
      x <<= 1;
      if (x & 0x100) x ^= DM_PRIM;
    }
    for (let i = 255; i < 512; i++) gfExp[i] = gfExp[i - 255];
  })();
  function gfMul(a, b) {
    if (!a || !b) return 0;
    return gfExp[gfLog[a] + gfLog[b]];
  }

  // Reed-Solomon 生成多項式の事前計算
  // ISO/IEC 16022 Annex E: g(x) = ∏_{i=1}^{degree} (x - α^i)
  // すなわち α^1, α^2, ..., α^degree を根とする。
  function rsGeneratorPoly(degree) {
    let poly = [1];
    for (let i = 0; i < degree; i++) {
      const newPoly = new Array(poly.length + 1).fill(0);
      for (let j = 0; j < poly.length; j++) {
        newPoly[j] ^= poly[j];
        newPoly[j + 1] ^= gfMul(poly[j], gfExp[i + 1]); // α^(i+1): 1-indexed
      }
      poly = newPoly;
    }
    return poly;
  }

  // Reed-Solomon 符号化: データから訂正符号を生成
  function rsEncode(data, eccLen) {
    const gen = rsGeneratorPoly(eccLen);
    const ecc = new Array(eccLen).fill(0);
    for (let i = 0; i < data.length; i++) {
      const factor = data[i] ^ ecc[0];
      ecc.shift();
      ecc.push(0);
      if (factor !== 0) {
        for (let j = 0; j < eccLen; j++) {
          ecc[j] ^= gfMul(gen[j + 1], factor);
        }
      }
    }
    return ecc;
  }

  // ===== エンコード (ASCII + Base256) =====
  // ASCII mode:
  //   - 値 0-127 (ASCII): codeword = value + 1
  //   - 値 128-255: upper shift (codeword=235) + (value - 128 + 1)
  //   - 数字2桁 (0-99): codeword = value + 130 (今回は使用しない、単純実装)
  //   - PAD: codeword = 129
  // Base256 mode:
  //   - 先頭に 231 (Base256 latch)
  //   - 続いて length (1 or 2 バイト, 擬似ランダム化)
  //   - 続いてデータバイト (擬似ランダム化)

  // Base256 の擬似ランダム化
  function b256Pseudo(byte, pos) {
    const pr = (149 * pos) % 255 + 1;
    const t = byte + pr;
    return t > 255 ? t - 256 : t;
  }

  // バイト列を Data Matrix コード語列に符号化 (Base256 モード)
  // 日本語など非ASCII文字は Base256 の方がコンパクトなので、一律 Base256 を使う
  function encodeBase256(bytes) {
    const out = [];
    // Base256 latch
    out.push(231);
    // length
    const len = bytes.length;
    let lenPos = out.length;
    if (len <= 249) {
      out.push(len);
    } else {
      out.push(Math.floor(len / 250) + 249);
      out.push(len % 250);
    }
    // data (pseudo-randomized, position starts from 1 after B256 latch)
    // position is 1-indexed from start of the whole codeword stream
    // ただし擬似ランダムは「Base256 latch 後の各コード語の位置」でなく、
    // 「シンボルデータコード語ストリームにおけるそのバイトの位置(1-indexed)」を使う
    // 今回は簡単化のため out.length をそのまま使う
    // → length 自体も擬似ランダム化が必要
    // 規格通りに書き直す:
    const result = [231]; // latch
    // length をエンコード
    if (len <= 249) {
      result.push(b256Pseudo(len, result.length + 1));
    } else {
      result.push(b256Pseudo(Math.floor(len / 250) + 249, result.length + 1));
      result.push(b256Pseudo(len % 250, result.length + 1));
    }
    // data
    for (let i = 0; i < bytes.length; i++) {
      result.push(b256Pseudo(bytes[i], result.length + 1));
    }
    return result;
  }

  // ASCII モードでの単純符号化 (0-127 のみ、ただし数字2桁最適化はスキップ)
  function encodeASCII(bytes) {
    const out = [];
    for (let i = 0; i < bytes.length; i++) {
      const b = bytes[i];
      if (b < 128) {
        out.push(b + 1);
      } else {
        // upper shift (ASCII モードでも 128 以上は上位シフトで表現可能)
        out.push(235); // upper shift
        out.push(b - 128 + 1);
      }
    }
    return out;
  }

  // UTF-8 バイト列に変換
  function toUtf8Bytes(str) {
    if (typeof TextEncoder !== 'undefined') {
      return new TextEncoder().encode(str);
    }
    // フォールバック
    const bytes = [];
    for (let i = 0; i < str.length; i++) {
      let code = str.charCodeAt(i);
      if (code < 0x80) bytes.push(code);
      else if (code < 0x800) {
        bytes.push(0xC0 | (code >> 6));
        bytes.push(0x80 | (code & 0x3F));
      } else {
        bytes.push(0xE0 | (code >> 12));
        bytes.push(0x80 | ((code >> 6) & 0x3F));
        bytes.push(0x80 | (code & 0x3F));
      }
    }
    return new Uint8Array(bytes);
  }

  // ===== モジュール配置アルゴリズム (ECC200) =====
  // ISO/IEC 16022 Annex F のアルゴリズム

  // 1 つのユーティリティモジュールを配置
  function dmPlaceModule(array, nrow, ncol, row, col, bit) {
    let r = row, c = col;
    if (r < 0) { r += nrow; c += 4 - ((nrow + 4) % 8); }
    if (c < 0) { c += ncol; r += 4 - ((ncol + 4) % 8); }
    if (r >= nrow || c >= ncol) return; // 範囲外は無視(コーナーケース)
    array[r][c] = bit;
  }

  // 1 個のユーティリティコード語を配置 (1 utah shape = 8 bits)
  function dmPlaceUtah(array, nrow, ncol, row, col, charIdx, codewords) {
    const byte = codewords[charIdx] || 0;
    for (let i = 0; i < 8; i++) {
      const bit = (byte >> (7 - i)) & 1;
      let dr, dc;
      // Utah shape の 8 ビット配置(相対座標)
      switch (i) {
        case 0: dr = row - 2; dc = col - 2; break;
        case 1: dr = row - 2; dc = col - 1; break;
        case 2: dr = row - 1; dc = col - 2; break;
        case 3: dr = row - 1; dc = col - 1; break;
        case 4: dr = row - 1; dc = col    ; break;
        case 5: dr = row    ; dc = col - 2; break;
        case 6: dr = row    ; dc = col - 1; break;
        case 7: dr = row    ; dc = col    ; break;
      }
      dmPlaceModule(array, nrow, ncol, dr, dc, bit);
    }
  }

  // コーナー用特殊配置 (4種類)
  function dmPlaceCorner1(array, nrow, ncol, charIdx, codewords) {
    const byte = codewords[charIdx] || 0;
    for (let i = 0; i < 8; i++) {
      const bit = (byte >> (7 - i)) & 1;
      let r, c;
      switch (i) {
        case 0: r = nrow - 1; c = 0; break;
        case 1: r = nrow - 1; c = 1; break;
        case 2: r = nrow - 1; c = 2; break;
        case 3: r = 0; c = ncol - 2; break;
        case 4: r = 0; c = ncol - 1; break;
        case 5: r = 1; c = ncol - 1; break;
        case 6: r = 2; c = ncol - 1; break;
        case 7: r = 3; c = ncol - 1; break;
      }
      array[r][c] = bit;
    }
  }
  function dmPlaceCorner2(array, nrow, ncol, charIdx, codewords) {
    const byte = codewords[charIdx] || 0;
    for (let i = 0; i < 8; i++) {
      const bit = (byte >> (7 - i)) & 1;
      let r, c;
      switch (i) {
        case 0: r = nrow - 3; c = 0; break;
        case 1: r = nrow - 2; c = 0; break;
        case 2: r = nrow - 1; c = 0; break;
        case 3: r = 0; c = ncol - 4; break;
        case 4: r = 0; c = ncol - 3; break;
        case 5: r = 0; c = ncol - 2; break;
        case 6: r = 0; c = ncol - 1; break;
        case 7: r = 1; c = ncol - 1; break;
      }
      array[r][c] = bit;
    }
  }
  function dmPlaceCorner3(array, nrow, ncol, charIdx, codewords) {
    const byte = codewords[charIdx] || 0;
    for (let i = 0; i < 8; i++) {
      const bit = (byte >> (7 - i)) & 1;
      let r, c;
      switch (i) {
        case 0: r = nrow - 3; c = 0; break;
        case 1: r = nrow - 2; c = 0; break;
        case 2: r = nrow - 1; c = 0; break;
        case 3: r = 0; c = ncol - 2; break;
        case 4: r = 0; c = ncol - 1; break;
        case 5: r = 1; c = ncol - 1; break;
        case 6: r = 2; c = ncol - 1; break;
        case 7: r = 3; c = ncol - 1; break;
      }
      array[r][c] = bit;
    }
  }
  function dmPlaceCorner4(array, nrow, ncol, charIdx, codewords) {
    const byte = codewords[charIdx] || 0;
    for (let i = 0; i < 8; i++) {
      const bit = (byte >> (7 - i)) & 1;
      let r, c;
      switch (i) {
        case 0: r = nrow - 1; c = 0; break;
        case 1: r = nrow - 1; c = ncol - 1; break;
        case 2: r = 0; c = ncol - 3; break;
        case 3: r = 0; c = ncol - 2; break;
        case 4: r = 0; c = ncol - 1; break;
        case 5: r = 1; c = ncol - 3; break;
        case 6: r = 1; c = ncol - 2; break;
        case 7: r = 1; c = ncol - 1; break;
      }
      array[r][c] = bit;
    }
  }

  // データコード語をマッピング領域全体に配置 (ECC200 placement algorithm)
  function dmBuildMatrix(nrow, ncol, codewords) {
    // -1: 未配置, 0 or 1: bit
    const array = [];
    for (let r = 0; r < nrow; r++) {
      array[r] = new Array(ncol).fill(-1);
    }
    let charIdx = 0;
    let row = 4;
    let col = 0;
    do {
      // コーナー特殊配置
      if (row === nrow && col === 0) {
        dmPlaceCorner1(array, nrow, ncol, charIdx++, codewords);
      } else if (row === nrow - 2 && col === 0 && ncol % 4 !== 0) {
        dmPlaceCorner2(array, nrow, ncol, charIdx++, codewords);
      } else if (row === nrow - 2 && col === 0 && ncol % 8 === 4) {
        dmPlaceCorner3(array, nrow, ncol, charIdx++, codewords);
      } else if (row === nrow + 4 && col === 2 && ncol % 8 === 0) {
        dmPlaceCorner4(array, nrow, ncol, charIdx++, codewords);
      }
      // 右上方向へ移動しながら utah shape 配置
      do {
        if (row < nrow && col >= 0 && array[row][col] < 0) {
          dmPlaceUtah(array, nrow, ncol, row, col, charIdx++, codewords);
        }
        row -= 2;
        col += 2;
      } while (row >= 0 && col < ncol);
      row += 1; col += 3;
      // 左下方向へ移動しながら utah shape 配置
      do {
        if (row >= 0 && col < ncol && array[row][col] < 0) {
          dmPlaceUtah(array, nrow, ncol, row, col, charIdx++, codewords);
        }
        row += 2;
        col -= 2;
      } while (row < nrow && col >= 0);
      row += 3; col += 1;
    } while (row < nrow || col < ncol);
    // 右下コーナー未配置の場合のパターン
    if (array[nrow - 1][ncol - 1] < 0) {
      array[nrow - 1][ncol - 1] = 1;
      array[nrow - 2][ncol - 2] = 1;
      array[nrow - 1][ncol - 2] = 0;
      array[nrow - 2][ncol - 1] = 0;
    }
    return array;
  }

  // データ領域(マッピング)行列を、最終シンボル(ファインダー・クロック付)に変換
  function assembleFinalSymbol(symbol, mappingArray) {
    const { size, regions } = symbol;
    const [rRows, rCols] = regions;
    const regionDataRows = symbol.mapping / rRows;
    const regionDataCols = symbol.mapping / rCols;

    const cells = [];
    for (let r = 0; r < size; r++) {
      cells[r] = new Array(size).fill(0);
    }

    // 各データ領域を配置 (各領域は外周1セルの「L字 + clock」で囲まれる)
    // 領域 (ri, ci) の配置先:
    //   開始行 = ri * (regionDataRows + 2)
    //   開始列 = ci * (regionDataCols + 2)
    for (let ri = 0; ri < rRows; ri++) {
      for (let ci = 0; ci < rCols; ci++) {
        const r0 = ri * (regionDataRows + 2);
        const c0 = ci * (regionDataCols + 2);
        // クロックパターン(上・右)を先に: 交互パターン
        // 上: (i)が偶数で黒、奇数で白。左隅(i=0)=黒、右隅(i=regionDataCols+1)= (cols+1)が偶なら黒
        for (let i = 0; i < regionDataCols + 2; i++) {
          cells[r0][c0 + i] = (i % 2 === 0) ? 1 : 0;
        }
        // 右: 下から黒で上に向かって交互。i=regionDataRows+1 (最下) が黒になるように。
        for (let i = 0; i < regionDataRows + 2; i++) {
          cells[r0 + i][c0 + regionDataCols + 1] =
            ((regionDataRows + 1 - i) % 2 === 0) ? 1 : 0;
        }
        // L字ファインダー(左・下): 全て黒（クロックと重なる隅も上書き）
        for (let i = 0; i < regionDataCols + 2; i++) {
          cells[r0 + regionDataRows + 1][c0 + i] = 1; // bottom row
        }
        for (let i = 0; i < regionDataRows + 2; i++) {
          cells[r0 + i][c0] = 1; // left col
        }
        // 実データ領域を充填
        for (let dr = 0; dr < regionDataRows; dr++) {
          for (let dc = 0; dc < regionDataCols; dc++) {
            const mr = ri * regionDataRows + dr;
            const mc = ci * regionDataCols + dc;
            const v = mappingArray[mr][mc];
            cells[r0 + 1 + dr][c0 + 1 + dc] = (v > 0) ? 1 : 0;
          }
        }
      }
    }
    return cells;
  }

  // ===== ECC ブロック化とインターリーブ =====
  // 1 ブロックの場合は単純に data の後ろに ecc を連結
  // 複数ブロックの場合はインターリーブ (ISO/IEC 16022 5.5.1)
  function buildFinalCodewords(symbol, dataCodewords) {
    const { data: dataCap, ecc: eccCap, blocks } = symbol;
    const eccPerBlock = eccCap / blocks;
    // データを「ブロック番号 b から始めて blocks 刻み」で拾ってブロック分割 → 各ブロックで RS 符号化
    const dataBlocks = [];
    const eccBlocks = [];
    for (let b = 0; b < blocks; b++) {
      const blockData = [];
      for (let i = b; i < dataCap; i += blocks) {
        blockData.push(dataCodewords[i] || 0);
      }
      dataBlocks.push(blockData);
      eccBlocks.push(rsEncode(blockData, eccPerBlock));
    }
    const finalCw = [];
    if (blocks === 1) {
      // 単一ブロック: データそのまま + ECC
      for (let i = 0; i < dataCap; i++) finalCw.push(dataCodewords[i] || 0);
      for (let i = 0; i < eccPerBlock; i++) finalCw.push(eccBlocks[0][i]);
    } else {
      // 複数ブロック: データ・ECC どちらもインターリーブ (ISO/IEC 16022 5.5.1)
      const maxDataLen = Math.max(...dataBlocks.map(d => d.length));
      for (let i = 0; i < maxDataLen; i++) {
        for (let b = 0; b < blocks; b++) {
          if (i < dataBlocks[b].length) finalCw.push(dataBlocks[b][i]);
        }
      }
      for (let i = 0; i < eccPerBlock; i++) {
        for (let b = 0; b < blocks; b++) {
          finalCw.push(eccBlocks[b][i]);
        }
      }
    }
    return finalCw;
  }

  // ===== DataMatrixCode クラス =====
  function DataMatrixCode() {
    this._data = new Uint8Array(0);
    this._mgmtBits32 = null;
    this._extBlocks = [];
    this._locationExt48 = null;
    this._municipalityExt24 = null;
    this._xorMask = null;
    this._forcedSize = null; // 指定された場合のみそのサイズを使う

    this._symbol = null;
    this._cells = null;
    this._codewords = null;   // データコード語 (管理部・拡張含む最終形)
    this._finalCw = null;     // データ+ECC 全コード語
  }

  DataMatrixCode.prototype.addData = function(text, mode) {
    if (text === undefined || text === null) return;
    const bytes = toUtf8Bytes(String(text));
    const merged = new Uint8Array(this._data.length + bytes.length);
    merged.set(this._data, 0);
    merged.set(bytes, this._data.length);
    this._data = merged;
  };

  DataMatrixCode.prototype.setManagementBits = function(bits32) {
    this._mgmtBits32 = bits32 >>> 0;
  };

  DataMatrixCode.prototype.setManagementExtBlocks = function(extBlocks) {
    this._extBlocks = extBlocks || [];
  };

  DataMatrixCode.prototype.setLocationExt48 = function(val) {
    this._locationExt48 = val;
  };

  DataMatrixCode.prototype.setMunicipalityExt24 = function(val) {
    this._municipalityExt24 = val;
  };

  DataMatrixCode.prototype.setXorMaskBytes = function(maskBytes) {
    this._xorMask = maskBytes;
  };

  DataMatrixCode.prototype.setSize = function(size) {
    this._forcedSize = size;
  };

  // 管理部・拡張管理部を含むコード語列を構築
  // 配置順（QR Twin Generator と同一）:
  //   (1) 通常データ (Base256)
  //   (2) codeword 129 (区切り)
  //   (3) 管理部32ビット (= 4バイト)
  //   (4) 拡張管理部 (extBlocks + location48 + municipality24)
  //   (5) codeword 129 (区切り)
  //   (6) 埋め草 (PAD codeword 129 の繰り返し)
  DataMatrixCode.prototype._buildCodewords = function(symbol) {
    const out = [];
    // (1) 通常データ: Base256 エンコード
    if (this._data && this._data.length > 0) {
      const encoded = encodeBase256(this._data);
      for (const c of encoded) out.push(c);
    }
    // (2) 区切り codeword 129
    out.push(129);
    // (3) 管理部 32 ビット (4 バイト)
    if (this._mgmtBits32 !== null) {
      out.push((this._mgmtBits32 >>> 24) & 0xFF);
      out.push((this._mgmtBits32 >>> 16) & 0xFF);
      out.push((this._mgmtBits32 >>> 8) & 0xFF);
      out.push(this._mgmtBits32 & 0xFF);
    }
    // (4) 拡張管理部
    for (const blk of this._extBlocks) {
      const bits = blk.bits >>> 0;
      const bitCount = blk.bitCount || 32;
      const byteCount = Math.ceil(bitCount / 8);
      for (let i = 0; i < byteCount; i++) {
        const shift = (byteCount - 1 - i) * 8;
        out.push((bits >>> shift) & 0xFF);
      }
    }
    if (this._locationExt48 !== null && this._locationExt48 !== undefined) {
      // 読取位置48ビット: lat(24bit) + lon(24bit) = 配列 [latVal, lonVal]
      let latVal, lonVal;
      if (Array.isArray(this._locationExt48)) {
        latVal = this._locationExt48[0] & 0xFFFFFF;
        lonVal = this._locationExt48[1] & 0xFFFFFF;
      } else {
        // 48ビット数値（JSでは精度問題があるため下位32+上位16で分割）
        const v = Number(this._locationExt48);
        latVal = Math.floor(v / 0x1000000) & 0xFFFFFF;
        lonVal = (v & 0xFFFFFF) >>> 0;
      }
      // 24ビット緯度（3バイト）
      out.push((latVal >>> 16) & 0xFF);
      out.push((latVal >>> 8) & 0xFF);
      out.push(latVal & 0xFF);
      // 24ビット経度（3バイト）
      out.push((lonVal >>> 16) & 0xFF);
      out.push((lonVal >>> 8) & 0xFF);
      out.push(lonVal & 0xFF);
    }
    if (this._municipalityExt24 !== null && this._municipalityExt24 !== undefined) {
      const v = this._municipalityExt24 >>> 0;
      out.push((v >>> 16) & 0xFF);
      out.push((v >>> 8) & 0xFF);
      out.push(v & 0xFF);
    }
    // (5) 区切り codeword 129
    out.push(129);
    // (6) 埋め草は _padToCapacity() でシンボル決定後に追加
    return out;
  };

  DataMatrixCode.prototype._padToCapacity = function(codewords, capacity) {
    // Data Matrix の埋め草規則 (ISO/IEC 16022 5.2.8):
    //   最初の PAD は 129 (リテラル)。
    //   2番目以降の PAD は擬似ランダム化 R = ((149 * P) mod 253) + 1,
    //     pad = 129 + R; if pad > 254: pad -= 254
    //   (P はコード語位置, 1始まり)
    const out = codewords.slice(0);
    let first = true;
    while (out.length < capacity) {
      if (first) {
        out.push(129);
        first = false;
      } else {
        const pos = out.length + 1; // 1-indexed position
        const R = ((149 * pos) % 253) + 1;
        let pad = 129 + R;
        if (pad > 254) pad -= 254;
        out.push(pad & 0xFF);
      }
    }
    return out;
  };

  DataMatrixCode.prototype.make = function() {
    // (A) コード語列構築 (埋め草を除く)
    const rawCw = this._buildCodewords(null);
    // (B) シンボル自動選択
    let symbol;
    if (this._forcedSize) {
      symbol = getSymbolBySize(this._forcedSize);
      if (rawCw.length > symbol.data) {
        throw new Error("指定されたサイズにデータが収まりません: " +
          rawCw.length + " > " + symbol.data);
      }
    } else {
      symbol = selectSymbol(rawCw.length);
    }
    // (C) 埋め草追加
    const dataCw = this._padToCapacity(rawCw, symbol.data);
    // (D) Reed-Solomon ECC + インターリーブ
    const finalCw = buildFinalCodewords(symbol, dataCw);
    // (E) XOR マスク適用 (ユーザ暗号化)
    if (this._xorMask && this._xorMask.length > 0) {
      for (let i = 0; i < finalCw.length; i++) {
        finalCw[i] = finalCw[i] ^ this._xorMask[i % this._xorMask.length];
      }
    }
    // (F) モジュール配置 (マッピング領域)
    const mapping = dmBuildMatrix(symbol.mapping, symbol.mapping, finalCw);
    // (G) 最終シンボル組立 (ファインダー・クロック追加)
    this._cells = assembleFinalSymbol(symbol, mapping);
    this._symbol = symbol;
    this._codewords = dataCw;
    this._finalCw = finalCw;
    return this;
  };

  DataMatrixCode.prototype.getModuleCount = function() {
    return this._symbol ? this._symbol.size : 0;
  };

  DataMatrixCode.prototype.isDark = function(row, col) {
    if (!this._cells) return false;
    if (row < 0 || row >= this._cells.length) return false;
    if (col < 0 || col >= this._cells[0].length) return false;
    return this._cells[row][col] === 1;
  };

  DataMatrixCode.prototype.getMatrix = function() {
    return this._cells;
  };

  DataMatrixCode.prototype.getTotalCodeCount = function() {
    return this._symbol ? (this._symbol.data + this._symbol.ecc) : 0;
  };

  DataMatrixCode.prototype.getDataCodeCount = function() {
    return this._symbol ? this._symbol.data : 0;
  };

  DataMatrixCode.prototype.getRSBlockInfo = function() {
    if (!this._symbol) return null;
    return {
      dataCount: this._symbol.data,
      eccCount: this._symbol.ecc,
      blocks: this._symbol.blocks
    };
  };

  DataMatrixCode.prototype.getCodewords = function() {
    return this._finalCw;
  };

  // ===== Factory =====
  // datamatrix(size) — size を指定しない場合は自動
  function datamatrix(size) {
    const dm = new DataMatrixCode();
    if (size) dm.setSize(size);
    return dm;
  }

  // シンボルサイズの一覧取得 (バージョン自動選択用)
  datamatrix.SYMBOLS = DM_SYMBOLS;
  datamatrix.getSymbol = getSymbolBySize;
  datamatrix.selectSymbol = selectSymbol;

  global.datamatrix = datamatrix;

})(typeof window !== 'undefined' ? window : (typeof global !== 'undefined' ? global : this));
