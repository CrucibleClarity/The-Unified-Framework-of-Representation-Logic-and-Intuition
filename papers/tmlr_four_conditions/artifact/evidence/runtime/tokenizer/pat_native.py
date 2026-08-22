"""
tokenizer/pat_native.py —— pat 原生 tokenizer 架构 (R141/R150)
=============================================================

用户指令 (2026-08-13): 重构 tokenizer 为 pat 原生架构.

原理 (量化精度探索 keahas-0.11):
  ctx 过长 = token 信息载体未优化.
  pat 原生: token = 相位量化格点 (2πj/N 槽环, R141).
  每 token 信息量 = log2(N) bits; 误差 ≤ π/N.

架构:
  PatNativeTokenizer
    ├── PatTokenV: 值 → 格点 (量化) / 格点 → 相位 (R141)
    ├── PhaseToken: 相位编码 (多层精度选择)
    ├── PatSequence: 序列编码 (变精度: 高频高 N, 低频低 N)
    └── CtxCompressor: ctx 压缩 (同信息更少 token)

与现有 tokenizer (concept_token/symbol_tokens) 的关系:
  现有: 概念 token (eid) — 语义层.
  pat 原生: 数值/相位 token (格点) — 表示层 (P 层).
  融合: 概念 token 定义经 pat 格点编码 (存算一体 R057).
"""

from __future__ import annotations
import math
import random
from typing import Dict, List, Optional, Tuple

TAU = 2 * math.pi


class PatTokenV:
    """pat 原生 token: 值 → 量化格点 (R141).

    编码: 值 x ∈ [0, 2π) → j = round(x·N/2π) mod N (量化到 N 槽环).
    解码: j → 相位 2πj/N.
    信息量: log2(N) bits; 误差 ≤ π/N.
    """

    def __init__(self, N: int = 16):
        self.N = N
        self.bits = math.log2(N)
        self.max_err = math.pi / N

    def encode(self, x: float) -> int:
        x = x % TAU
        return round(x * self.N / TAU) % self.N

    def decode(self, j: int) -> float:
        return TAU * (j % self.N) / self.N

    def __repr__(self):
        return f"PatTokenV(N={self.N}, {self.bits:.1f}bits, err≤{self.max_err:.4f})"


class PhaseToken:
    """相位 token: 多层精度 (高频 token 高精度, 低频低精度).

    频率自适应量化: 使用频率高的 token 用高 N (低误差),
    低频 token 用低 N (省空间) — ctx 优化.
    """

    def __init__(self):
        self.freq: Dict[str, int] = {}
        self.precision: Dict[str, int] = {}
        self.PRECISIONS = [4, 8, 16, 32, 64]

    def note_use(self, token_id: str):
        self.freq[token_id] = self.freq.get(token_id, 0) + 1
        # 自适应精度: 频率越高精度越高 (最多 64)
        f = self.freq[token_id]
        idx = min(f // 10, len(self.PRECISIONS) - 1)
        self.precision[token_id] = self.PRECISIONS[idx]

    def precision_of(self, token_id: str) -> int:
        return self.precision.get(token_id, 16)

    def encode(self, token_id: str, x: float) -> int:
        self.note_use(token_id)
        return PatTokenV(self.precision_of(token_id)).encode(x)

    def __repr__(self):
        return f"PhaseToken({len(self.freq)} token, 精度分布 {sorted(set(self.precision.values()))})"


class PatSequence:
    """pat 序列编码: 变精度序列 (每个 token 独立精度)."""

    def __init__(self):
        self.phase = PhaseToken()

    def encode_sequence(self, tokens: List[Tuple[str, float]]) -> List[Dict]:
        """编码: [(token_id, value)] → [格点编码] (先记频率后取精度)."""
        out = []
        for tid, val in tokens:
            self.phase.note_use(tid)
            N = self.phase.precision_of(tid)
            j = PatTokenV(N).encode(val)
            out.append({"token": tid, "slot": j, "N": N,
                        "phase": TAU * j / N})
        return out

    def bits_total(self, seq: List[Dict]) -> float:
        """总信息量 (bits)."""
        return sum(math.log2(e["N"]) for e in seq)

    def __repr__(self):
        return f"PatSequence(变精度编码)"


class CtxCompressor:
    """ctx 压缩: 同信息量, 高精度需更少 token.

    压缩比 = 平均 bits/token 提升.
    量化精度探索 (keahas-0.11): N=16→4bits, N=64→6bits ⟹ 1.5× 压缩.
    """

    def __init__(self, base_N: int = 16):
        self.base_N = base_N
        self.base_bits = math.log2(base_N)

    def compress_ratio(self, N: int) -> float:
        """相对 base 的压缩比 (每 token 载更多信息)."""
        return math.log2(N) / self.base_bits

    def estimate_ctx(self, n_tokens: int, N: int) -> float:
        """等价 ctx (相对 base_N 的同信息 token 数)."""
        return n_tokens * self.base_bits / math.log2(N)

    def __repr__(self):
        return f"CtxCompressor(base_N={self.base_N})"


class PatNativeTokenizer:
    """pat 原生 tokenizer: token = 相位量化格点 (R141/R150).

    与现有 tokenizer 融合:
      概念 token (eid, 语义层) → 相位格点编码 (表示层 P).
      ctx 优化: 量化精度 N 自适应 (频率/结构驱动).
    """

    def __init__(self, base_N: int = 16):
        self.base_N = base_N
        self.tok = PatTokenV(base_N)
        self.phase = PhaseToken()
        self.seq = PatSequence()
        self.compressor = CtxCompressor(base_N)

    def encode_value(self, x: float) -> int:
        """值 → 格点 (基础精度)."""
        return self.tok.encode(x)

    def decode_value(self, j: int) -> float:
        return self.tok.decode(j)

    def encode_sequence(self, token_value_pairs: List[Tuple[str, float]]) -> List[Dict]:
        """序列编码 (变精度)."""
        return self.seq.encode_sequence(token_value_pairs)

    def ctx_estimate(self, n_tokens: int, N: int = None) -> float:
        """ctx 估算: 同信息等价 token 数."""
        N = N or self.base_N
        return self.compressor.estimate_ctx(n_tokens, N)

    def __repr__(self):
        return (f"PatNativeTokenizer(base_N={self.base_N})\n"
                f"  {self.tok}\n  {self.phase}\n  {self.seq}\n  {self.compressor}")
