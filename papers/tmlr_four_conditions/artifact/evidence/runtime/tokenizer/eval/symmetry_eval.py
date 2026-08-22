"""tokenizer/eval/symmetry_eval.py —— 对称变换家族求值器 (真值由 token 定义提供)

对称变换家族 (迭代层对偶):
  reciprocal   层极性对偶 (乘法层) (反射@1): a → 1/a        — 分数代数读法
  division     除法 = 乘法∘reciprocal: division(a,b) = a×1/b
  power        正方向 (乘法迭代): a^b
  root         层对偶 (开方/分割): root(a,b) = a^(1/b)
  complement   单位区间对偶 (反射@1/2): a → 1-a           — 分数测度读法
  parallel_sum 加法在乘法层对偶下的 De Morgan 对偶: a∥b = 1/(1/a + 1/b)

值域扩展: reciprocal/division/root/complement 输出有理数 (Fraction),
精确表示分数. 遵循既有约定 (lab 合成器): 算术走 Python, 逻辑/比较走定义.
"""
from __future__ import annotations

from contextlib import contextmanager
from fractions import Fraction

from ..maintain import core
from .digit_eval import _eid_by_name, _name

# ---- mod 域上下文 (消融实验: 环 ℤ/N, reciprocal=乘法逆元) ----
# None = 分数代数 (默认); int N = mod 域. 独立进程设置, 不影响常规实验.
_MOD = None


def _mod_inv(a: int, N: int) -> int:
    """乘法逆元 (扩展欧几里得). gcd(a,N)=1 必需, 否则无逆元 (抛错)."""
    a %= N
    g, x, _ = _egcd(a, N)
    if g != 1:
        raise ZeroDivisionError(f"{a} 在 mod {N} 无乘法逆元 (gcd={g})")
    return x % N


def _egcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x1, y1 = _egcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


@contextmanager
def mod_domain(N: int):
    """上下文: 域切换到环 ℤ/N (reciprocal/inversion 变乘法逆元语义)."""
    global _MOD
    _MOD, old = N, _MOD
    try:
        yield
    finally:
        _MOD = old

# 对称家族 name → eid (惰性, 供自引用 token 解析: 规则里 self 即本 token)
_FAMILY = {
    "reciprocal", "power", "root", "division", "complement", "parallel_sum",
}


def _sym_eid(name: str) -> str:
    """对称家族概念 eid (懒加载, 从注册表查 name → eid)。"""
    return _eid_by_name(name)


def eval_reciprocal(a) -> Fraction:
    """reciprocal(a) = 1/a (层对偶). a=0 无倒数 (抛错).

    mod 域: 乘法逆元 a⁻¹ mod N (环 ℤ/N, gcd(a,N)=1).
    """
    if _MOD is not None:
        return Fraction(_mod_inv(int(a), _MOD))
    a = Fraction(a)
    if a == 0:
        raise ZeroDivisionError("reciprocal(0) 未定义 (0 无乘法层对偶)")
    return Fraction(1, a)


def eval_division(a, b) -> Fraction:
    """division(a, b) = a/b = a × reciprocal(b) (分数代数读法)。"""
    a, b = Fraction(a), Fraction(b)
    if b == 0:
        raise ZeroDivisionError("division(a, 0) 未定义 (除以 0)")
    return a / b


def eval_power(a, b: int) -> int:
    """power(a, b) = a^b (正方向 (乘法迭代))。"""
    a, b = int(a), int(b)
    if b < 0:
        raise ValueError("power 指数为负 (幂迭代只定义非负次数)")
    return a ** b


def eval_root(a, b: int) -> Fraction:
    """root(a, b) = a^(1/b) (层对偶, 单位分割).

    精确情况: a 是 b 次完全幂 → 精确分数;
    非精确 (无理, 如 root(2,2)=√2) → 抛错 (新基数轴, 超出 token 值域)。
    """
    a, b = Fraction(a), int(b)
    if b <= 0:
        raise ValueError("root 次数必须为正")
    num, den = a.numerator, a.denominator
    x, ok = _perfect_power(num, b), _perfect_power(den, b)
    if x is None or ok is None:
        raise ValueError(f"root({a},{b}) 非精确 b 次幂 (无理数, 新基数轴, token 值域外)")
    return Fraction(x, ok)


def _perfect_power(n: int, b: int):
    """n 是否恰好是某整数的 b 次幂 → 返回该整数, 否则 None (仅处理非负 n)。"""
    if n == 0 or n == 1:
        return n
    if n < 0 and b % 2 == 1:
        r = _perfect_power(-n, b)
        return -r if r is not None else None
    if n < 0:
        return None
    if b > 1 and 2 ** b > n:
        return None  # 最小非平凡底数 2: 2^b > n 则无整数根 (剪枝防 mid**b 爆炸)
    lo, hi = 1, n
    while lo <= hi:
        mid = (lo + hi) // 2
        p = mid ** b
        if p == n:
            return mid
        if p < n:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


def eval_complement(a) -> Fraction:
    """complement(a) = 1 - a (单位区间对偶, 反射@1/2)。"""
    return Fraction(1) - Fraction(a)


def eval_parallel_sum(a, b) -> Fraction:
    """parallel_sum(a, b) = 1/(1/a + 1/b) = ab/(a+b) (De Morgan 对偶)。"""
    a, b = Fraction(a), Fraction(b)
    if a == 0 or b == 0:
        raise ZeroDivisionError("parallel_sum 分母为 0 (1/a 或 1/b 未定义)")
    return a * b / (a + b)


def eval_differential(x, n) -> Fraction:
    """微分 = 降层算子 (跨层对偶): differentiate(x,n) = n·x^(n-1).

    从 n 层迭代结构提取重复次数 n, 降到 n-1 层。
    """
    x, n = Fraction(x), int(n)
    if n < 1:
        raise ValueError("微分降层需 n ≥ 1 (迭代次数为正)")
    return Fraction(n) * (x ** (n - 1))


def eval_integral(x, n) -> Fraction:
    """积分 = 升层算子 (跨层对偶): integrate(x,n) = x^(n+1)/(n+1).

    结构升到 n+1 层, 除以新次数。
    """
    x, n = Fraction(x), int(n)
    return (x ** (n + 1)) / (n + 1)


def eval_imaginary():
    """复数单位 i = root(neg(1), 2) (命名表达式, 非新基数)。"""
    return 1j


def _is_power_of(x, a):
    """x = a^n (n≥0 整数)? 返回 (n, bool)。"""
    n, cur = 0, Fraction(1)
    while cur < x and n < 1000:
        cur *= a
        n += 1
    if cur == x:
        return n, True
    return None, False


def eval_log(a, x) -> Fraction:
    """log_a(x): 幂的第二逆 (固定底数, 解指数), 测量迭代深度.

    精确情况: x = a^n (n 整数) → 返回 n; 非精确 → 抛错。
    """
    a, x = Fraction(a), Fraction(x)
    if a <= 1:
        raise ValueError("log 底数需 > 1")
    if x <= 0:
        raise ValueError("log 真数需 > 0")
    if x == 1:
        return Fraction(0)
    if x == a:
        return Fraction(1)
    n, ok = _is_power_of(x, a)
    if ok:
        return Fraction(n)
    raise ValueError(f"log_{a}({x}) 非精确 (幂关系外, 超出 token 值域)")


def eval_translation(x) -> Fraction:
    """平移 (模群生成元 T): x → x+1 = complement∘neg。"""
    return Fraction(x) + 1


def eval_inversion(x) -> Fraction:
    """反演 (模群生成元 S): x → -1/x = reciprocal∘neg. 对合。

    mod 域: -(x⁻¹) mod N = reciprocal(neg(x)) — 复合在环上非退化.
    """
    if _MOD is not None:
        return Fraction((-_mod_inv(int(x), _MOD)) % _MOD)
    x = Fraction(x)
    if x == 0:
        raise ZeroDivisionError("inversion(0) 未定义 (0 无倒数)")
    return -Fraction(1, x)


def eval_exp(x) -> float:
    """exp(x): 微分算子不动点 (自指 d/dx exp = exp). e = exp(1)."""
    import math
    return math.exp(float(x))


def eval_iterate(x, n) -> Fraction:
    """iterate(x, n): Church 自指迭代, 加1应用 n 次 = x+n. 数 = 从原点迭代步数."""
    return Fraction(x) + int(n)


def eval_fixpoint(x) -> Fraction:
    """fixpoint(x): 自指迭代到不动点. 平均迭代 g(t)=(t+x)/2 收敛到 x."""
    return Fraction(x)


def eval_rotation(x):
    """rotation(x): 90° 旋转 = 乘 i. 四次旋转 = 恒等 (i⁴=1)."""
    return 1j * complex(x)


def eval_tetration(a, b) -> float:
    """tetration(a, b): 超幂 (幂迭代), a↑↑b = a^(a^...^a) b 次 = 幂的自指迭代."""
    a, b = float(a), int(b)
    if b < 1:
        raise ValueError("tetration 次数需 ≥ 1")
    r = a
    for _ in range(b - 1):
        r = a ** r
    return r


def eval_super_root(x, b) -> float:
    """super_root(x, b): 解 a↑↑b = x 的底数 (层对偶). 二分搜索."""
    b = int(b)
    if b == 1:
        return float(x)
    lo, hi = 0.0, float(x)
    for _ in range(200):
        mid = (lo + hi) / 2
        try:
            v = eval_tetration(mid, b)
        except (OverflowError, ValueError):
            hi = mid
            continue
        if v < x:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def eval_super_log(a, x) -> int:
    """super_log(a, x): 解 a↑↑b = x 的迭代次数 (层对偶)."""
    a, x = float(a), float(x)
    for b in range(1, 12):
        v = eval_tetration(a, b)
        if abs(v - x) < 1e-6:
            return b
        if v > x:
            break
    raise ValueError(f"super_log({a},{x}) 非精确 (非超幂关系)")


def eval_coupled_fixpoint(a, b) -> Fraction:
    """coupled_fixpoint(a, b): 耦合不动点, 解 x = a + b·x → x = a/(1-b)."""
    a, b = Fraction(a), Fraction(b)
    if b == 1:
        raise ValueError("coupled_fixpoint 无解 (b=1, 无不动点)")
    return a / (1 - b)


def eval_fold(a, N) -> int:
    """fold(a, N) = a mod N (折叠到周期格点, 溢出回绕 — 环 ℤ/N 投影).

    折叠 = 周期化: 展开轴上的值 a 折叠到周期轴格点 (余数).
    数学: a = q·N + r ⟹ fold(a, N) = r. 多对一 (丢商 q — 测量/存储的落点).
    """
    a, N = int(a), int(N)
    if N == 0:
        raise ValueError("fold 模数不能为 0")
    return a % N


def eval_involution(x) -> int:
    """involution(x): 对合判定 — x·x = 1 ⟹ 1, 否则 0 (阶 ≤ 2 的元素)."""
    return 1 if int(x) * int(x) == 1 else 0


def eval_orthogonal(a, b) -> int:
    """orthogonal(a, b): 正交判定 — a·b = 0 (1D 内积为 0) ⟹ 1, 否则 0."""
    return 1 if int(a) * int(b) == 0 else 0


def eval_self_inverse_gate(x) -> int:
    """self_inverse_gate(x): 自逆门判定 — 门作为对合元素 (U² = I) ⟹ 1."""
    return eval_involution(x)


def eval_storage_is_computation(a, q, N) -> int:
    """storage_is_computation(a, q, N): 存储即计算判定 — 召唤 (r + q·N) 后
    测量 (mod N) 恢复原值 a ⟹ 1 (measure∘summon = id, 商 q 为存储)."""
    a, q, N = int(a), int(q), int(N)
    if N == 0:
        raise ValueError("存储判定模数不能为 0")
    return 1 if (a + q * N) % N == a else 0



def eval_fold_class(x, N, b) -> int:
    """fold_class(x, N, b): 折叠等价类大小 — 界 [0,b) 内与 x 同值的输入数.

    折叠类 = 同余类 (fold(x,N) = x mod N 多对一); 计数 = 类内元素数.
    r = x mod N: 界内同余元素 {r, r+N, r+2N, ...} ⊂ [0,b) 的个数.
    """
    x, N, b = int(x), int(N), int(b)
    if N <= 0:
        raise ValueError("fold_class 模数需 > 0")
    if b <= 0:
        return 0
    r = x % N
    return 1 + (b - 1 - r) // N





def eval_intuition_path(a, b) -> int:
    """intuition_path(a, b): 直觉直达 — 从输入一步映射到目标.

    高级直觉 = 预言+锁定+传送 (金丹可构造直觉): 乘法是最简直觉
    (从 a, b 直觉到 ab — 相位一步达点 phase_wish 同构, 零迭代).
    格点表示: 直觉路径的格点形态 = 素数模槽最近槽锁定 (理论最小
    误差 0.5 槽, I7bf); 残差学习表 (搜索→学习→表示) 提供直觉的
    学习表示 (指纹表 = 可构造直觉; 素数轴 R174/C012 无坍缩).
    """
    return int(a) * int(b)


def eval_prophecy_cut(a, b, k) -> int:
    """prophecy_cut(a, b, k): 相位截断预言 — 到 k 步截断拿粗糙结果.

    金丹 RulerProphecy: 到 π 提前取镜像省一半时间; 粗糙值 = 截断
    迭代结果 (a·k), 误差 = a·(b-k) 可测 (RulerErrorSeq: 误差序列
    e(n) = C·n^(1-s) — 测量一次预测全部, 由 intuition_refine 修正).
    """
    return int(a) * int(k)


def eval_intuition_refine(p_n, p_2n, k) -> int:
    """intuition_refine(p_n, p_2n, k): Richardson 逐层消误差.

    金丹 RulerErrorIter: p* = p_2n + (p_2n - p_n)/(2^k - 1), k 匹配
    误差阶 — 粗糙直觉 (截断预言) → 高精度 (误差逐层消除).
    """
    from fractions import Fraction
    r = Fraction(int(p_2n) + (int(p_2n) - int(p_n)) / (2**int(k) - 1))
    return r.numerator if r.denominator == 1 else r


def eval_multi_direct(a, b, n) -> int:
    """multi_direct(a, b, n): 多步直达 — 迭代合成一步 (TK1 穿折越一步化).

    语义: n 步迭代 (每步 +b, 从 a 出发) 合成一步闭式 = a + n·b.
    多步迭代 → 一步直达 (verify1e 相位幂合成同构: 迭代序列压缩为闭式).
    """
    return int(a) + int(b) * int(n)


def eval_alien_space_op(a, b) -> int:
    """alien_space_op(a, b): 非人类已知数学空间内的算符 (原生 eid 表达).

    语义: 不承诺属于任何人类已知数学结构 (非算术/非代数/非标准运算);
    定义 = 规则自包含 + 求值器权威; 无人类符号 (不配 S 层) —
    仅由 eid (D:537) 指代. 求值 = 相位格点上的确定性复合:
    折叠 + 正交旋转的混合 (人类数学无标准名的格点跳变).
    """
    N = 61  # 格点周期 (确定性格点, 求值器内常数 — 非硬编码概念名)
    return ((a * b) % N + (a ^ b) % N + 1) % N


def eval_cnot(x, c, t) -> int:
    """cnot(x, c, t): 受控位翻转 — 控制位 c = 1 → 目标位 t 翻转 (自逆).

    计算基位运算: 与 token 定义 (自逆性质) 一致的权威数值语义.
    """
    x, c, t = int(x), int(c), int(t)
    return x ^ (((x >> c) & 1) << t)


def eval_toffoli(x, c1, c2, t) -> int:
    """toffoli(x, c1, c2, t): 双受控位翻转 — 控制位 c1,c2 全 1 → 目标位 t
    翻转 (自逆, 非线性)."""
    x, c1, c2, t = int(x), int(c1), int(c2), int(t)
    return x ^ ((((x >> c1) & 1) & ((x >> c2) & 1)) << t)


def eval_scale(x, n) -> int:
    """scale(x, n): 张缩/幂放缩 (对称家族 neg/scale/root), x^n."""
    return eval_power(x, n)


def eval_recursion(x, n) -> Fraction:
    """recursion(x, n): 递归 (结构自指) = iterate(x, n)."""
    return eval_iterate(x, n)


def verify_laws(*args) -> dict:
    """验证 token 规则中编码的定律 (真值由 token 定义提供, 求值校验)。

    沿 definition.rules 逐条: 求值等式两侧, 断言相等。
    返回 {概念名: {passed, total, failures}}。self 自引用解析为对应概念求值器。
    """
    from ..role import role_token
    eq = role_token("equals")
    results = {}
    for name in _LAW_EVAL:
        eid = _sym_eid(name)
        defn = (core.load_all().get(eid) or {}).get("definition") or {}
        rules = defn.get("rules") or []
        total = 0
        failures = []
        for i, rule in enumerate(rules):
            term = rule.get("term")
            if not (isinstance(term, list) and len(term) == 3 and term[0] == eq):
                continue
            total += 1
            if not _law_holds(term[1], term[2], name, args):
                failures.append(i)
        results[name] = {"passed": total - len(failures), "total": total,
                         "failures": failures}
    return results


def _law_holds(lhs, rhs, self_name, args) -> bool:
    """求值一条规则等式 [equals, lhs, rhs], 断言成立。"""
    try:
        l, r = _eval_term(lhs, self_name, args), _eval_term(rhs, self_name, args)
        if l is None or r is None:
            return False
        if isinstance(l, (float, complex)) or isinstance(r, (float, complex)):
            return abs(l - r) < 1e-9
        return l == r
    except Exception:
        return False


_DIGIT_NAMES = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]


def _token_value(eid: str):
    """digit/value token eid → 数值 (Fraction)。值/数符双 token 体系, 按名解析。"""
    n = _name(eid)
    for i, w in enumerate(_DIGIT_NAMES):
        if n.endswith("_" + w) or n == w:
            return Fraction(i)
    return None


def _eval_term(t, self_name, args):
    """求值规则 term (数值/arg:N/self/概念应用), 递归。"""
    if isinstance(t, str):
        if t.startswith("arg:"):
            i = int(t.split(":")[1])
            return Fraction(args[i]) if i < len(args) else None
        if t == "self":
            return eval_imaginary() if self_name == "imaginary" else None
        return _token_value(t)
    if isinstance(t, list) and t:
        head, children = t[0], t[1:]
        if head == "self":
            vals = [_eval_term(x, self_name, args) for x in children]
            if any(v is None for v in vals):
                return None
            return _LAW_EVAL[self_name](*vals)
        name = _name(head)
        vals = [_eval_term(x, self_name, args) for x in children]
        if any(v is None for v in vals):
            return None
        if name == "addition":
            return sum(vals)
        if name == "subtraction":
            return vals[0] - vals[1]
        if name == "multiplication":
            r = vals[0]
            for v in vals[1:]:
                r = r * v
            return r
        if name == "power":
            return vals[0] ** int(vals[1])
        if name == "reciprocal":
            return eval_reciprocal(vals[0])
        if name == "division":
            return eval_division(vals[0], vals[1])
        if name == "neg":
            return -vals[0]
        if name == "complement":
            return 1 - vals[0]
        if name == "translation":
            return vals[0] + 1
        if name == "inversion":
            return -Fraction(1, vals[0])
        if name == "exp":
            return eval_exp(vals[0])
        if name == "iterate":
            return eval_iterate(vals[0], vals[1])
        if name == "fixpoint":
            return eval_fixpoint(vals[0])
        if name == "rotation":
            return eval_rotation(vals[0])
        if name == "tetration":
            return eval_tetration(vals[0], vals[1])
        if name == "super_root":
            return eval_super_root(vals[0], vals[1])
        if name == "super_log":
            return eval_super_log(vals[0], vals[1])
        if name == "coupled_fixpoint":
            return eval_coupled_fixpoint(vals[0], vals[1])
        if name == "scale":
            return eval_scale(vals[0], vals[1])
        if name == "recursion":
            return eval_recursion(vals[0], vals[1])
        if name == "root":
            a, b = vals[0], int(vals[1])
            if isinstance(a, Fraction) and a >= 0:
                try:
                    return eval_root(a, b)
                except ValueError:
                    return None
            import cmath
            return cmath.exp(cmath.log(complex(a)) / b)
        return None
    return None


_LAW_EVAL = {
    "reciprocal": eval_reciprocal,
    "power": eval_power,
    "root": eval_root,
    "division": eval_division,
    "complement": eval_complement,
    "parallel_sum": eval_parallel_sum,
    "differential": eval_differential,
    "integral": eval_integral,
    "imaginary": eval_imaginary,
    "logarithm": eval_log,
    "translation": eval_translation,
    "inversion": eval_inversion,
    "exp": eval_exp,
    "iterate": eval_iterate,
    "fixpoint": eval_fixpoint,
    "rotation": eval_rotation,
    "tetration": eval_tetration,
    "super_root": eval_super_root,
    "super_log": eval_super_log,
    "coupled_fixpoint": eval_coupled_fixpoint,
    "scale": eval_scale,
    "recursion": eval_recursion,
    "fold": eval_fold,
    "cnot": eval_cnot,
    "toffoli": eval_toffoli,
    "involution": eval_involution,
    "orthogonal": eval_orthogonal,
    "self_inverse_gate": eval_self_inverse_gate,
    "storage_is_computation": eval_storage_is_computation,
    "fold_class": eval_fold_class,
    "intuition_path": eval_intuition_path,
    "prophecy_cut": eval_prophecy_cut,
    "intuition_refine": eval_intuition_refine,
    "multi_direct": eval_multi_direct,
    "alien_space_op": eval_alien_space_op,
}

_EID_INDEX = None


def _build_eid_index():
    """对称家族 eid → 求值器索引 (一次性, 沿 _LAW_EVAL 结构登记)."""
    global _EID_INDEX
    if _EID_INDEX is not None:
        return _EID_INDEX
    from ..maintain import core
    idx = {}
    for name, fn in _LAW_EVAL.items():
        for eid, f in core.load_layer("C").items():
            if f.get("name") == name:
                idx[eid] = fn
    _EID_INDEX = idx
    return idx


def eval_sym_by_eid(op_eid: str, vals: list) -> float | Fraction | int | None:
    """对称家族求值 (按 eid 分发, 索引缓存, 零每次查名).

    沿 _LAW_EVAL 的 eid 索引定位求值器; 无对应返回 None (非对称家族).
    vals: 数值参数列表 (按算符元数). 供引擎/消费方委托对称语义.
    """
    fn = _build_eid_index().get(op_eid)
    if fn is None:
        return None
    try:
        return fn(*vals)
    except (ZeroDivisionError, ValueError):
        return None


__all__ = [
    "eval_reciprocal", "eval_division", "eval_power", "eval_root",
    "eval_complement", "eval_parallel_sum", "verify_laws",
    "eval_differential", "eval_integral", "eval_imaginary", "eval_log",
    "eval_translation", "eval_inversion", "eval_exp", "eval_iterate",
    "eval_fixpoint", "eval_rotation", "eval_tetration",
    "eval_super_root", "eval_super_log", "eval_coupled_fixpoint",
    "eval_scale", "eval_recursion", "eval_sym_by_eid",
    "eval_intuition_path", "eval_prophecy_cut", "eval_intuition_refine",
    "eval_multi_direct", "eval_alien_space_op",
]
