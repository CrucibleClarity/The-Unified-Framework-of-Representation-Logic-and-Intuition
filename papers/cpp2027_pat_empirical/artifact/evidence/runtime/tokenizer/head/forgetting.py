"""
head/forgetting.py —— tokenizer 注意力优化: 遗忘曲线 + 连接池 (keahas-0.8 融合)
============================================================================

优化动机 (用户指令 2026-08-13: 尝试优化 tokenizer 体系):
  1. 遗忘曲线作为反馈循环: token 使用频率随时间衰减 → 注意力权重调节
     (低频 token 注意力衰减 = 适度遗忘; 高频 token 复习巩固)
  2. 连接池管理: token 间连接 (引用链) 复用/回收 — 不重复解析

融入 keahas-0.8 (ForgettingCurve + ConnectionPool) 到 tokenizer head:
  - ForgettingCurve: token 访问频率衰减, 反馈低频 token (需巩固的)
  - ConnectionPool: token 引用连接 (定义链) 池化复用

只经权威接口 (construct/expand + _register), 不建平行访问.
"""

from __future__ import annotations
import math
import os
import random
import time
from typing import Dict, List, Optional, Tuple

from .._register import token_of
from ..construct.expand import bracket_vec, brace_logic, brace_derived


# ============================================================
# tokenizer 遗忘曲线 (token 使用频率衰减)
# ============================================================

class TokenForgettingCurve:
    """token 遗忘曲线: 使用频率指数衰减 → 注意力权重.

    Ebbinghaus: strength(t) = strength0 · e^(-λ·Δt).
    高使用 token: 复习巩固 (strength 高, 注意力权重高).
    低使用 token: 遗忘 (strength 低, 注意力权重低 = 适度遗忘).
    反馈: 衰减边缘 token = 需要复习的信号.
    """

    def __init__(self, decay_rate: float = 0.02):
        self.decay = decay_rate
        self.strength: Dict[str, float] = {}   # eid → 强度
        self.last_seen: Dict[str, float] = {}  # eid → 最后访问
        self.visit: Dict[str, int] = {}        # eid → 访问次数
        self.time = 0.0
        self.reviewed = 0
        self.forgotten = 0

    def visit_token(self, eid: str):
        """访问 token: 强度 +, 时间更新 (复习巩固)."""
        self.time += 1.0
        self.visit[eid] = self.visit.get(eid, 0) + 1
        if eid in self.strength:
            self.strength[eid] = min(self.strength[eid] + 0.1, 1.0)
            self.reviewed += 1
        else:
            self.strength[eid] = 0.8
        self.last_seen[eid] = self.time

    def weight(self, eid: str) -> float:
        """注意力权重: 按遗忘曲线衰减后的强度.

        高使用 token (近期访问) → 权重高; 长期未用 → 衰减 (适度遗忘).
        """
        if eid not in self.strength:
            return 0.1
        dt = self.time - self.last_seen[eid]
        s = self.strength[eid] * math.exp(-self.decay * dt)
        return max(s, 0.05)  # 最低注意力 (不消失, 只衰减)

    def feedback(self, threshold: float = 0.4) -> List[str]:
        """遗忘反馈: 衰减到阈值以下的 token = 需要复习巩固.

        适度遗忘 = 反馈循环: 低频 token 提升注意力或复习.
        """
        signals = []
        for eid, s in self.strength.items():
            dt = self.time - self.last_seen[eid]
            st = s * math.exp(-self.decay * dt)
            if st < threshold:
                signals.append(eid)
        return signals

    def forget(self, threshold: float = 0.1) -> int:
        """遗忘: 极低频 token 从强度表释放 (资源)."""
        keep = {}
        for eid, s in self.strength.items():
            dt = self.time - self.last_seen[eid]
            if s * math.exp(-self.decay * dt) >= threshold:
                keep[eid] = s
            else:
                self.forgotten += 1
        self.strength = keep
        return self.forgotten

    def __repr__(self):
        return f"TokenForgettingCurve(token={len(self.strength)}, 复习={self.reviewed}, 遗忘={self.forgotten})"


# ============================================================
# tokenizer 连接池 (token 引用连接复用)
# ============================================================

class TokenConnectionPool:
    """token 连接池: 定义链/引用连接复用与回收.

    token 间连接 = 定义引用 (eid → 被引用 eids, bracket_vec).
    池化: 已解析的连接复用 (不重复 expand); 低流量连接回收.
    """

    def __init__(self, max_conn: int = 128):
        self.conns: Dict[Tuple[str, str], float] = {}  # (from, to) → 流量
        self.max_conn = max_conn
        self.reused = 0
        self.allocated = 0

    def link(self, src: str, dst: str):
        """连接: 建立/复用 (定义引用关系)."""
        key = (src, dst)
        if key in self.conns:
            self.conns[key] = min(self.conns[key] + 0.1, 5.0)
            self.reused += 1
        elif len(self.conns) < self.max_conn:
            self.conns[key] = 0.1
            self.allocated += 1

    def connections_of(self, eid: str) -> List[Tuple[str, str]]:
        """取 eid 的全部连接 (出边)."""
        return [(a, b) for (a, b) in self.conns if a == eid]

    def recycle(self, threshold: float = 0.05) -> int:
        """回收低流量连接."""
        keep = {k: v for k, v in self.conns.items() if v >= threshold}
        n = len(self.conns) - len(keep)
        self.conns = keep
        return n

    def __repr__(self):
        return f"TokenConnectionPool(conns={len(self.conns)}, 复用={self.reused})"


# ============================================================
# 优化入口: 融合遗忘曲线 + 连接池 的注意力分析
# ============================================================

class TokenizerAttentionV8:
    """tokenizer 注意力优化 (keahas-0.8 融合).

    analyze: 每 token 的注意力权重 = 结构信号 (brace/bracket) × 遗忘曲线权重.
    """

    def __init__(self):
        self.forget = TokenForgettingCurve(decay_rate=0.02)
        self.pool = TokenConnectionPool()

    def analyze(self, sequence: List[str], ctx: Optional[dict] = None) -> List[dict]:
        """概念 eid 序列 → 注意力分析 (含遗忘权重 + 连接池).

        sequence: 概念 eid 列表.
        每 token: {eid, name, bracket, brace, counts, attn_weight}.
        attn_weight = 结构信号 (brace 深度) × 遗忘曲线权重 (使用频率).
        """
        rows, seen = [], set()
        for e in sequence:
            if e in seen:
                continue
            seen.add(e)
            # 访问 (遗忘曲线复习)
            self.forget.visit_token(e)
            # 结构信号 (定义链)
            bd = brace_derived(e)
            # 连接池 (引用连接)
            for ref in bracket_vec(e):
                if isinstance(ref, str):
                    self.pool.link(e, ref)
            # 注意力权重: 结构 × 频率 (遗忘曲线)
            structure_sig = min(len(brace_logic(e)), 3) / 3.0 + 0.1
            freq_w = self.forget.weight(e)
            rows.append({
                "eid": e,
                "name": token_of(e).name,
                "bracket": bracket_vec(e),
                "brace": brace_logic(e),
                "counts": {k: v for k, v in bd.items() if v > 0},
                "attn_weight": round(structure_sig * freq_w, 4),
                "freq_weight": round(freq_w, 4),
            })
        return rows

    def feedback(self) -> List[str]:
        """遗忘反馈: 需巩固的 token (低频)."""
        return self.forget.feedback()

    def prune(self) -> Dict:
        """遗忘 + 连接回收 (资源管理)."""
        forgotten = self.forget.forget()
        recycled = self.pool.recycle()
        return {"forgotten_tokens": forgotten, "recycled_conns": recycled}

    def __repr__(self):
        return (f"TokenizerAttentionV8\n  {self.forget}\n  {self.pool}")
