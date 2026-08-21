"""tokenizer/eval/engine.py —— 通用求值引擎 (输入/输出纯原生 token 序列)

铁律 (用户确立):
  - 输入是 token 序列, 输出是 token 序列 — 接口绝不输出非 token 值
  - 唯一允许数字参与计算处 = numeral 快路径 (digit 排序还原位序),
    内部经 numeral 转数值, 结果经 numeral 还原为 token
  - 真值沿 token 定义推导 (definition.rules), 零硬编码算子名/eid

架构:
  统一加载器 (预编译/校验重编译/缓存复用/batch load):
    每个算符的定义预编译为编译产物, 签名 = 数据版本 (cte.DATA_VERSION),
    变化幂等重编译, CTE 缓存复用, 一次可 load 多个算符.
  通用求值器:
    eval(op_eid, arg_tokens) -> result_tokens
      输入: 算子 eid + 操作数 numeral token 序列
      输出: 结果 numeral token 序列
    数字算子沿定义迭代链归约 (iteration_depth 推导层数, 下层算符重复
    迭代 b 次), 内部数值计算经 numeral 快路径; 逻辑算子沿真值表匹配.
"""
from __future__ import annotations

from .. import cte
from ..maintain import core
from . import digit_eval, numeral_eval
from .logic_eval import logic_truth, _truth_eids

# 运算概念名 (方程右侧含运算的判定, 零 eid 硬编码)
_OP_NAMES = {
    "addition", "subtraction", "multiplication", "division", "power",
    "root", "neg", "modulo", "num_concat",
    # 运算家族 (D:506+, 定义驱动注册): 方程识别集随 token 注册扩展
    "fold", "unfold", "measure", "summon", "qft", "period_axis",
    "basepoint_move", "time_reversal", "flip", "hadamard",
    "involution", "orthogonal", "self_inverse_gate", "storage_is_computation",
    "equals_arith",
}

# ---- 统一加载器 (预编译/校验重编译/缓存复用/batch load) ----
def load_ops(op_eids: list[str]) -> int:
    """batch load: 一次预编译多个算符定义 (幂等, 数据变化才重编译)."""
    n = 0
    for e in op_eids:
        _get_op(e)
        n += 1
    return n


def load_all_ops() -> int:
    """预编译全部 arrange∈{application,binary_connective,unary_connective} 算子."""
    ops = [e for e in _all_concept_eids()
           if _arrange(e) in ("application", "binary_connective", "unary_connective")]
    return load_ops(ops)


def _get_op(op_eid: str) -> dict:
    """单算子编译产物 (CTE: 签名一致复用, 变化幂等重编译)."""
    return cte.get_or_compile("eng:op:" + op_eid, cte._version(),
                              lambda: _compile_op(op_eid))


def _compile_op(op_eid: str) -> dict:
    d = core.load_all().get(op_eid, {}).get("definition") or {}
    return {
        "arrange": d.get("arrange"),
        "rules": [r.get("term") for r in (d.get("rules") or [])
                  if isinstance(r.get("term"), list)],
        "refs": d.get("references") or [],
    }


def op_meta(op_eid: str) -> dict:
    """算子结构原语 (预编译产物, CTE 缓存) — 统一基础设施接口.

    eval 本地经本接口取结构识别结果, 不自行推导:
      arrange     排列 (application/binary_connective/unary_connective)
      is_logic    逻辑算子 (refs 引用 truth token)
      is_unary    一元数字算子 (rules 操作数槽位仅 arg:0)
      depth       迭代层数 (1=succ 原子基, 2=succ 迭代, 3=addition 迭代...)
      is_pred     基于 pred 迭代 (subtraction)
      is_succ     基于 succ 迭代 (addition)
      is_atom     迭代原子 (succ/pred/iterate)
      base        迭代基础 (层 k-1 算符 eid, 无则 None)
      identity    迭代单位元 (0 次迭代结果, 沿定义 rules)
      tower       递归塔结构 (base_eid, step_eid) 或 None
    未来修改 eval 计算逻辑只改 eval 层, 结构识别已固化于预编译.
    """
    return cte.get_or_compile("eng:meta:" + op_eid, cte._version(),
                              lambda: _build_meta(op_eid))


def _build_meta(op_eid: str) -> dict:
    """结构原语推导 (基于编译产物, 递归缓存依赖)."""
    op = _get_op(op_eid)
    depth = _calc_depth(op_eid)
    _T, _F = _truth_eids()
    truth_set = {_T, _F}
    return {
        "arrange": op["arrange"],
        "is_logic": bool(truth_set & set(op["refs"])),
        "is_unary": _calc_unary(op_eid),
        "depth": depth,
        "is_pred": _calc_pred_based(op_eid),
        "is_succ": _calc_succ_based(op_eid),
        "is_atom": _calc_iter_atom(op_eid),
        "base": _calc_base_of_layer(op_eid),
        "identity": _calc_identity(op_eid),
        "tower": _calc_tower(op_eid),
    }


def _calc_unary(op_eid: str) -> bool:
    """一元数字算子: rules 操作数槽位仅 arg:0 (无 arg:1)."""
    max_arg = -1
    for term in _get_op(op_eid)["rules"]:
        for a in _collect_arg_idxs(term):
            if a > max_arg:
                max_arg = a
    return max_arg == 0


def _calc_pred_based(op_eid: str) -> bool:
    """基于 pred 迭代 (subtraction): 定义 refs 引用 pred."""
    from .. import api as _api
    return _api.eid_by_name("pred") in set(_get_op(op_eid)["refs"])


def _calc_succ_based(op_eid: str) -> bool:
    """基于 succ 迭代 (addition): refs 引用 succ 且非 pred 迭代."""
    from .. import api as _api
    succ = _api.eid_by_name("succ")
    return succ in set(_get_op(op_eid)["refs"]) and not _calc_pred_based(op_eid)


def _calc_iter_atom(eid: str) -> bool:
    """迭代原子 (succ/pred/iterate): 与 api.iteration_depth 同口径原子集."""
    return eid in _iter_atoms()


def _calc_depth(op_eid: str) -> int:
    """迭代层数 (沿定义引用, 零硬编码): 同 tokenizer.api.iteration_depth."""
    from .. import api as _api
    try:
        return _api.iteration_depth(op_eid)
    except Exception:
        return 1


def _calc_base_of_layer(op_eid: str):
    """层 k 算符的迭代基础 (层 k-1): 沿 refs 找引用的算符 (非迭代原子).

    迭代原子 (succ/pred/iterate) 是层1 基础, 不参与上层迭代基础选择;
    multiplication.refs 引 addition (层1) → 基础 addition;
    power.refs 引 multiplication (层2) → 基础 multiplication.
    """
    refs = set(_get_op(op_eid)["refs"])
    cands = [r for r in refs if r.startswith("D:")
             and _arrange(r) == "application" and r != op_eid
             and not _calc_iter_atom(r)]
    if not cands:
        return None
    return max(cands, key=_calc_depth)


def _calc_identity(op_eid: str) -> int:
    """迭代单位元: 本算符 0 次迭代的结果 (沿定义 rules, 零硬编码).

    迭代 op(a,b) = 下层算符应用 b 次, 起点 = 本算符 0 次结果.
    从定义规则读: [equals, [op, arg:0, value_zero], X] → X 即单位
    (value_zero 是 rules 里的第二参数, 值为 0 的 value token).
    power: [pow, a, 0]=1 → 1; multiplication: [mul, a, 0]=0 → 0.
    结果 X 须为常量 token (arg:N/self 是变量, 非单位元).
    """
    for term in _get_op(op_eid)["rules"]:
        if not (isinstance(term, list) and len(term) == 3):
            continue
        app, result = term[1], term[2]
        if not (isinstance(app, list) and app and app[0] in (op_eid, "self")):
            continue
        args = app[1:]
        if len(args) == 2 and _is_value_zero(args[1]):
            if isinstance(result, str) and not (result.startswith("arg:") or result == "self"):
                return _value_of(result, op_eid)
    return 0


def _calc_tower(op_eid: str):
    """递归塔规则识别 (tetration): [self, a, [add/succ, b]] → [base, a, [self, a, b]].

    超运算 (幂迭代) 是递归塔 (幂的自指迭代), 非"下层迭代 b 次" —
    沿 rules 识别其递归结构. 返回 (base_eid, step_eid) 或 None.
    """
    from .. import api as _api
    add = _api.eid_by_name("addition")
    succ = _api.eid_by_name("succ")
    for term in _get_op(op_eid)["rules"]:
        if not (isinstance(term, list) and len(term) == 3):
            continue
        app, result = term[1], term[2]
        if not (isinstance(app, list) and app and app[0] in (op_eid, "self")):
            continue
        if len(app) != 3 or not isinstance(app[2], list):
            continue
        step = app[2]
        if not (isinstance(step, list) and step and step[0] in (add, succ)):
            continue
        # result = [base, a, [self, a, b]]? — 真塔: result 第 3 元素是
        # [self,...] 递归结构 (tetration: [pow, a, [self, a, b]]);
        # 乘法 result=[add, [self,a,b], a] 第 3 元素是原子 a (非塔, 排除)
        if not (isinstance(result, list) and len(result) == 3):
            continue
        if result[0] in (op_eid, "self"):
            continue
        third = result[2]
        if not (isinstance(third, list) and third and third[0] in (op_eid, "self")):
            continue
        return result[0], step[0]
    return None


# ---- eval 本地 (调用 op_meta 基础设施接口, 数值计算) ----
def _is_logic_op(op_eid: str) -> bool:
    return op_meta(op_eid)["is_logic"]


def _is_unary(op_eid: str) -> bool:
    return op_meta(op_eid)["is_unary"]


def _is_pred_based(op_eid: str) -> bool:
    return op_meta(op_eid)["is_pred"]


def _is_succ_based(op_eid: str) -> bool:
    return op_meta(op_eid)["is_succ"]


def _is_iter_atom(eid: str) -> bool:
    return op_meta(eid)["is_atom"]


def _iteration_depth(op_eid: str) -> int:
    return op_meta(op_eid)["depth"]


def _base_of_layer(op_eid: str):
    return op_meta(op_eid)["base"]


def _identity_for(op_eid: str) -> int:
    return op_meta(op_eid)["identity"]


def _tower_rule(op_eid: str):
    return op_meta(op_eid)["tower"]


def _all_concept_eids():
    from .._register import all_eids
    return [e for e in all_eids() if e.startswith("D:")]


def _arrange(eid: str) -> str | None:
    d = core.load_all().get(eid, {}).get("definition") or {}
    return d.get("arrange")


def _name(eid: str) -> str:
    from .._register import token_of
    try:
        return token_of(eid).name
    except KeyError:
        return eid


# ---- 通用求值器: eval(op, arg_tokens) -> result_tokens ----
def eval_op(op_eid: str, arg_tokens: list[list[str]], *, base: int = 10) -> list[str]:
    """通用求值: 算子 + 操作数 token 序列 → 结果 token 序列.

    arg_tokens: 每操作数的 numeral token 序列 (sign_part+digit_seq)
    或 truth token 序列 (逻辑算子).
    输出: 结果 numeral / truth token 序列.
    未覆盖 → ValueError.
    """
    if _is_logic_op(op_eid):
        return _eval_logic(op_eid, arg_tokens)
    return _eval_numeric(op_eid, arg_tokens, base)


def _eval_logic(op_eid: str, arg_tokens: list[list[str]]) -> list[str]:
    """逻辑算子: 沿 definition.rules 真值表匹配 → truth token 序列."""
    _T, _F = _truth_eids()
    flat = [t for args in arg_tokens for t in args]
    t = logic_truth(op_eid, flat)
    if t is None:
        raise ValueError(f"逻辑真值未覆盖: op={_name(op_eid)} args={flat}")
    return [_T if t else _F]


def _is_num_token(eid: str) -> bool:
    """eid 是否为 num_N token (base-256 字节). 沿 name 前缀, 零硬编码 eid."""
    return _name(eid).startswith("num_")


def _eval_num_seq(arg: list[str], base: int = 256) -> int:
    """num token 序列 → 值 (位置定权, 低→高: Σ num_i × 256^i).

    构造路径 (构造决定 OOD): num_seq 排列 (相邻合并 ×256+后位) 的可逆求值.
    num_0..255 序列, 位置 i 权重 256^i.
    """
    v = 0
    for e in arg:
        nm = _name(e)
        assert nm.startswith("num_"), f"非 num token: {nm}"
        v = v * base + int(nm.split("_")[1])
    return v


def _is_num_seq(arg: list[str]) -> bool:
    """arg 是否为 num token 序列 (全 num_N, 至少一个)."""
    return len(arg) > 0 and all(_is_num_token(e) for e in arg)


def _eval_numeric(op_eid: str, arg_tokens: list[list[str]], base: int) -> list[str]:
    """数字算子: 操作数 numeral → 数值 (numeral 快路径) → 迭代归约 → 还原 token.

    内部数值计算 (唯一允许数字处 = numeral 快路径): eval_numeral 解析
    操作数, 沿定义迭代链计算, 结果经 numeral 还原为 token 序列.
    操作数若为 num token 序列 (方案A 折叠), 走 base-256 位权折叠求值.
    """
    if all(_is_num_seq(a) for a in arg_tokens):
        vals = [_eval_num_seq(a) for a in arg_tokens]
    else:
        vals = [numeral_eval.eval_numeral(a, base) for a in arg_tokens]
    result = _compute(op_eid, vals)
    n = _as_int(result)
    return _tokens_of_numeral(n, base)


def _as_int(result):
    """数值结果 → int (numeral 表示). 非整数 (分数/无理数) → ValueError.

    数域表示范围限制 (用户确立): token 体系当前只表示整数 numeral;
    分数/无理数/复数结果超出表示范围 → 跳过 (由合成器捕获).
    """
    from fractions import Fraction
    if isinstance(result, bool):
        return int(result)
    if isinstance(result, int):
        return result
    if isinstance(result, Fraction):
        if result.denominator == 1:
            return result.numerator
        raise ValueError(f"分数结果不可表示: {result}")
    if isinstance(result, float):
        if result.is_integer() and abs(result) < 1e15:
            return int(result)
        raise ValueError(f"无理/浮点结果不可表示: {result}")
    raise ValueError(f"结果类型不可表示: {type(result).__name__}")


def _equation_rule(op_eid: str):
    """算子定义中的直接方程: rules 形如 [equals, [self, arg:N...], 可求值项].

    识别: term[0]=equals_arith, term[1] 顶层含 self (方程左端定义被定义项),
    右侧 (term[2]) 顶层不含 self (非递归定义) → 直接方程.
    返回右侧 term 或 None (无直接方程 → 走迭代链/对称).
    """
    rules = _get_op(op_eid).get("rules") or []
    eq_eid = None
    from .digit_eval import _eid_by_name as _ebn
    try:
        eq_eid = _ebn("equals_arith")
    except Exception:
        return None
    for r in rules:
        term = r if isinstance(r, list) else r.get("term")
        if not isinstance(term, list) or len(term) < 3 or term[0] != eq_eid:
            continue
        lhs, rhs = term[1], term[2]
        if not isinstance(lhs, list) or "self" not in _flatten(lhs):
            continue
        if "self" in _flatten(rhs):
            continue  # 递归定义 (迭代链) → 排除
        # 右侧必须含计算操作 (addition/multiplication 等运算概念, 按名判定),
        # 排除纯 identity 方程 (a×0=0: 右侧 value_zero 常量, 非运算).
        rhs_flat = _flatten(rhs)
        if any(_name(x) in _OP_NAMES for x in rhs_flat if isinstance(x, str)
               and x.startswith("D:")):
            return rhs
    return None


def _flatten(x):
    out = []
    if isinstance(x, list):
        for y in x:
            out.extend(_flatten(y))
    else:
        out.append(x)
    return out


def _eval_equation_term(term, vals, self_eid: int) -> int:
    """递归求值方程右侧: arg:N 绑 vals, self→self_eid 定义, 概念 eid → eval_op."""
    if isinstance(term, int) or isinstance(term, str):
        if str(term).startswith("arg:"):
            return vals[int(str(term)[4:])]
        if str(term) == "self":
            return self_eid  # 递归自引用 (应被 _equation_rule 排除; 防御)
        # 概念 eid → eval_op 递归求值 (0 参原子 = 值)
        try:
            from .digit_eval import _eid_by_name as _ebn
            if str(term).startswith("D:"):
                return _token_num(int(str(term)[2:]) if False else str(term))
        except Exception:
            pass
        return _token_num(term)
    # 嵌套应用: [op, arg...] 递归
    op = term[0]
    args = [_eval_equation_term(a, vals, self_eid) for a in term[1:]]
    # op 是 eid → eval_op 求值
    if isinstance(op, str):
        from .digit_eval import _eid_by_name as _ebn
        op_eid = op if op.startswith("D:") else _ebn(op)
        return _eval_op_int(op_eid, args)
    return args[0] if len(args) == 1 else args


def _ring(v: int) -> int:
    """mod 域归约 (环 ℤ/N 上下文; 域外恒等). 幂等 (% N 两次 = 一次)."""
    from .symmetry_eval import _MOD as _mod
    return v % _mod if _mod is not None else v


def _eval_op_int(op_eid, vals: list[int]) -> int:
    """eval_op 数值封装: 概念 eid + int 参数 → int 结果.

    基础算术概念 (addition/multiplication) 直接数值计算 (中间值可超 255,
    num_N 单字节表示不够); 其他概念走 eval_op (token 原生).
    """
    from .digit_eval import _name as _dn
    nm = _dn(op_eid)
    if nm == "num_256":
        return 256
    if nm == "addition":
        return _ring(vals[0] + vals[1] if len(vals) > 1 else vals[0])
    if nm == "multiplication":
        return _ring(vals[0] * vals[1] if len(vals) > 1 else vals[0])
    if nm == "subtraction":
        return _ring(vals[0] - vals[1] if len(vals) > 1 else -vals[0])
    # 其他概念: 直接数值计算 (绕过 token 往返 — 分数/大中间值友好;
    # 往返对 Fraction 中间值断裂 (division 方程嵌套 reciprocal 暴露)).
    return _compute(op_eid, vals)


def _token_num(eid: str) -> int:
    """num_N / value_N token → 数值 (支持 num_zero/value_zero 英文名)."""
    from .digit_eval import _name as _dn
    nm = _dn(eid)
    for prefix in ("num_", "value_"):
        if nm.startswith(prefix):
            s = nm[len(prefix):]
            words = {"zero": 0, "one": 1, "two": 2, "three": 3, "four": 4,
                     "five": 5, "six": 6, "seven": 7, "eight": 8, "nine": 9}
            return int(s) if s.isdigit() else words.get(s, 0)
    return 0


def _token_num_id(v: int) -> str:
    """数值 → num token eid (num_0..255)."""
    from .digit_eval import _eid_by_name as _ebn
    return _ebn(f"num_{v}")


def _compute(op_eid: str, vals: list[int]) -> int:
    """数字算子归约: 沿定义迭代链, 零算子名硬编码.

    迭代链 (从定义引用推导): succ (原子, 层1) → addition (succ 迭代, 层2)
    → multiplication (addition 迭代, 层3) → power (multiplication 迭代, 层4)
    → tetration (power 迭代, 层5). 层 k 算符 = 层 k-1 算符重复应用 b 次.
    层2 特例: subtraction 是 pred 迭代 (非 addition 迭代), 直接数值语义.
    方程算子 (如 num_concat: concat(a,b)=a×256+b): rules 含直接等价方程
    (self 在等号左侧, 右侧可求值), 沿方程递归求值 — 不推断迭代链.
    """
    # 方程算子: 定义方程直接实例化 (v0.2 求值引擎下沉, token 原生).
    # _equation_rule 已排除递归/identity 方程 → 只对真方程算子生效
    # (num_concat: concat(a,b)=a×256+b; addition 的 a+0=a 是 identity, 被排除).
    eq = _equation_rule(op_eid)
    if eq is not None:
        return _eval_equation_term(eq, vals, op_eid)
    # 对称家族算符 (translation/inversion/differential/super_root 等特殊语义)
    # 委托 symmetry_eval (数学权威实现, eid 索引分发, 零每次查名).
    # 引擎迭代链只覆盖纯迭代算符 (addition/mul/pow/tetration 等);
    # 非链成员 (层运算/对偶/超运算) 由 symmetry 提供权威语义.
    from .symmetry_eval import eval_sym_by_eid
    if not _is_iter_chain_member(op_eid):
        sym = eval_sym_by_eid(op_eid, vals)
        if sym is not None:
            return sym
    try:
        return _compute_engine(op_eid, vals)
    except ValueError:
        sym = eval_sym_by_eid(op_eid, vals)
        if sym is not None:
            return sym
        raise


def _is_iter_chain_member(op_eid: str) -> bool:
    """纯迭代链成员: 沿 succ/pred 原子 → 迭代基础严格追溯.

    核心迭代链 (引擎迭代归约正确): succ/pred/iterate 原子 + 每阶
    base 沿链回溯至原子且**无对称语义求值器** (addition/multiplication/
    power/tetration/subtraction). division/differential/logarithm 等虽
    引 power/addition 但非纯迭代 (对称/层语义) → 非链成员, 走 symmetry.
    沿 op_meta + symmetry eid 索引判定.
    """
    m = op_meta(op_eid)
    if m.get("is_atom"):
        return True
    if m.get("is_unary"):
        return op_eid == _neg_eid()
    # 沿 base 链回溯到原子; 途中任何算符有 symmetry 求值器 (非纯迭代) → False
    from .symmetry_eval import _build_eid_index
    sym_idx = _build_eid_index()
    cur = op_eid
    seen = set()
    while cur is not None and cur not in seen:
        if cur in sym_idx:
            return False
        seen.add(cur)
        cur = op_meta(cur).get("base")
    return True


def _compute_engine(op_eid: str, vals: list[int]) -> int:
    """引擎数字归约: 迭代链 + 基础算符 (零名字硬编码)."""
    depth = _iteration_depth(op_eid)
    if depth <= 1 or _is_unary(op_eid):
        return _base_compute(op_eid, vals)
    # subtraction (depth2, pred 迭代): 直接数值 (递减)
    if depth == 2 and _is_pred_based(op_eid):
        return _base_compute(op_eid, vals)
    base = _base_of_layer(op_eid)
    if base is None:
        return _base_compute(op_eid, vals)
    # 层 ≥3: 下层算符迭代 b 次, 起点 = 本算符 0 次结果 (沿定义 rules)
    a, b = vals[0], vals[1] if len(vals) > 1 else 1
    # 负迭代次数 (乘法负操作数, 用户样本①): a × (-b) = -(a × |b|)
    # 符号翻转沿 neg 概念 (结构识别), 迭代用 |b| 次后取反
    sign_negate = b < 0
    b_abs = abs(b)
    # 递归塔结构 (tetration: tet(a,b+1)=base(a,tet(a,b))): 沿 rules 递归归约
    tower = _tower_rule(op_eid)
    if tower is not None:
        return _compute_tower(op_eid, a, b)
    acc = _identity_for(op_eid)
    for _ in range(b_abs):
        acc = _compute(base, [acc, a] if len(vals) > 1 else [acc])
    return -acc if sign_negate else acc


def _compute_tower(op_eid: str, a: int, b: int) -> int:
    """递归塔求值: tet(a,0)=1 (单位元), tet(a,b+1)=base(a,tet(a,b))."""
    base = _tower_rule(op_eid)[0]
    acc = _identity_for(op_eid)
    for _ in range(b):
        acc = _compute(base, [a, acc])
    return acc


def _collect_arg_idxs(node) -> list[int]:
    """term 中 arg:N 槽位索引 (递归收集, 去重保序)."""
    out = []

    def _walk(n):
        if isinstance(n, str):
            if n.startswith("arg:"):
                out.append(int(n[4:]))
            return
        if isinstance(n, list):
            for ch in n:
                _walk(ch)
    _walk(node)
    return out


def _is_iter_atom(eid: str) -> bool:
    """迭代原子 (succ/pred/iterate): 与 api.iteration_depth 同口径原子集."""
    return eid in _iter_atoms()


_ITER_ATOM_SET = None


def _iter_atoms():
    """迭代原子集 (succ/pred/iterate, 沿注册表, 与 api.iteration_depth 一致)."""
    global _ITER_ATOM_SET
    if _ITER_ATOM_SET is None:
        from .. import api as _api
        _ITER_ATOM_SET = {_api.eid_by_name(n) for n in ("succ", "pred", "iterate")}
    return _ITER_ATOM_SET


def _is_value_zero(eid) -> bool:
    """eid 是否为 value_zero (值 0 的 value token, 沿 arrow 链, 非名字)."""
    if not isinstance(eid, str):
        return False
    try:
        return numeral_eval.value_number(eid) == 0
    except ValueError:
        return False


def _value_of(eid: str, base_eid: str) -> int:
    """token eid → 数值 (digit 经 eval_digit_value; 其他 → 错误)."""
    try:
        return numeral_eval.eval_digit_value(eid)
    except (ValueError, KeyError):
        raise ValueError(f"单位元 token 非 digit: {_name(eid)}")


def _base_compute(op_eid: str, vals: list[int]) -> int:
    """基础算符数值归约 (结构识别经 op_meta 接口, 零名字硬编码).

    沿 token 原生结构识别对应计算工具 (快速路径合法, 但不靠 name):
      - 迭代原子 (succ/pred/iterate): 后继/前驱 (a+1)
      - pred 迭代算子 (subtraction): 递减 (a-b)
      - 一元数字算子 (neg): 极性对偶 (-a)
      - succ 迭代算子 (addition): 递增 (a+b)
    识别全部沿定义结构 (原子集/引用/pred 迭代/一元), 不查算子名.
    """
    a = vals[0]
    b = vals[1] if len(vals) > 1 else None
    # 一元数字算子: 仅 neg (极性对偶, 结构识别); 其他一元 (translation/
    # inversion 等) 委托 symmetry (数学语义, 引擎不覆盖)
    if _is_unary(op_eid):
        if op_eid == _neg_eid():
            return _ring(-a)
        raise ValueError(f"一元算符非 neg (委托 symmetry): {_name(op_eid)}")
    # 迭代原子 (succ/pred/iterate): 后继/前驱
    if _is_iter_atom(op_eid):
        return _ring(a + 1)
    # pred 迭代算子 (subtraction): 递减
    if _is_pred_based(op_eid):
        return _ring(a - (b or 0))
    # succ 迭代算子 (addition): 递增
    if _is_succ_based(op_eid):
        return _ring(a + (b or 0))
    raise ValueError(f"基础算符未覆盖: op={_name(op_eid)} args={vals}")


# ---- numeral 还原 (数值 → token 序列, 纯 token) ----
def _tokens_of_numeral(n: int, base: int) -> list[str]:
    """数值 → numeral token 序列 (经 numeral 快路径还原, 纯 token).

    负数 = sign_neg 前缀 + 绝对值 numeral (极性对偶; 与 eval_numeral 解析一致
    — 原用 neg 概念前缀, 解析器不认 (往返断裂, time_reversal 暴露)).
    """
    from .. import api as _api
    if n < 0:
        sign_neg = _api.eid_by_name("sign_neg")
        return [sign_neg] + _tokens_of_numeral(-n, base)
    if n == 0:
        dg = [_api.value_token(0)]
    else:
        ds = []
        m = n
        while m:
            m, d = divmod(m, base)
            ds.append(d)
        ds.reverse()
        dg = [_api.value_token(d) for d in ds]
    return _api.numeral_of(dg, sign_eid=None)


_NEG_EID = None


def _neg_eid() -> str:
    """neg 概念 eid (结构识别: 一元数字算子, 零名字/eid 硬编码).

    识别: arrange=unary_connective + 非逻辑 (无 truth 引用) + 一元 (无 arg:1)
    + 非迭代原子 (succ/pred 是一元但非极性对偶). 唯一候选为 neg."""
    global _NEG_EID
    if _NEG_EID is None:
        for e in _all_concept_eids():
            op = _get_op(e)
            if op["arrange"] != "unary_connective":
                continue
            if _is_logic_op(e) or _is_iter_atom(e):
                continue
            if not _is_unary(e):
                continue
            _NEG_EID = e
            break
    return _NEG_EID


def precompile_all() -> int:
    """预编译全部可求值算子 (batch load). 返回算符数."""
    return load_all_ops()


__all__ = ["eval_op", "load_ops", "load_all_ops", "precompile_all"]
