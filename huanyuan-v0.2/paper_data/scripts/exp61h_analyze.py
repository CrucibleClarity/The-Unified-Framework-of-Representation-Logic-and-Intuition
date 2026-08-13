"""EXP-61h 分析: clone_a vs clone_b 分布 (直觉均匀 vs 结构集中)."""
import torch, json
from tokenizer import api
from tokenizer.token_index import inject_temp, clear_cache, _TEMP_INJECT
from tokenizer.maintain import core
from tokenizer._register import DERIVE_REGISTRY, DERIVE_BY_NAME, load_derive
from train.data import vocab
from train.model import TokenTransformer
from lab import run_exp
from lab.judge import judge_sequence

# 注入 clone (恢复 vocab 487)
src = core.load_all()[api.eid_by_name("logical_and")]
defn = src.get("definition")
rows = [{"eid":"D:9001","name":"logical_and_c0","dtype":"bool","definition":defn},
        {"eid":"D:9002","name":"logical_and_c1","dtype":"bool","definition":defn}]
inject_temp("C", rows)
DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear(); load_derive(); clear_cache(); core._ALL_CACHE = None

V = vocab()
m = TokenTransformer(dim=64, num_concepts=len(V), num_layers=2, input_mode="ids", causal=False).eval()
m.load_state_dict(torch.load("/tmp/opencode/exp61h_model.pt", weights_only=False, map_location="cpu"))
def judge(seqs):
    ss = [{"seq": s, "valid": 1} for s in seqs]
    if len(ss) < 2: ss = ss + [{"seq": seqs[0], "valid": 1}]
    return run_exp._judge_eval(m, ss)[0]

_T = api.role_token("truth"); TRUE, FALSE = _T
C0, C1 = "D:9001", "D:9002"
# 逻辑门判定序列: [is_true][A][op][B][truth] (infix)
def mk(a, op, b, truth):
    return judge_sequence([TRUE if a else FALSE, op, TRUE if b else FALSE], truth)
# 全组合
seqs_c0 = [mk(a, C0, b, a and b) for a in (True, False) for b in (True, False)]
seqs_c1 = [mk(a, C1, b, a and b) for a in (True, False) for b in (True, False)]
seqs_mix = [mk(a, C0 if (a and b) else C1, b, a and b) for a in (True, False) for b in (True, False)]

print("=== EXP-61h: clone 分布分析 ===")
print(f"只用 c0 判定: {judge(seqs_c0):.3f}")
print(f"只用 c1 判定: {judge(seqs_c1):.3f}")
print(f"混合 c0/c1 判定: {judge(seqs_mix):.3f}")
# 注意力: 两 clone 在序列中被正确重建的比例 (直接看模型预测)
from train.data import collate, rev_vocab
rv = rev_vocab()
seq = seqs_mix[0]
batch = collate([{"seq": seq, "valid": 1}], input_mode="ids")
with torch.no_grad():
    logits, _ = m(batch["inputs"], mask=batch["mask"])
rl = batch["lengths"][0]
preds = [rv[p] for p in logits[0,:rl].argmax(dim=1).tolist()]
names = [api.name(x) for x in seq]
print("样本预测:", " ".join(preds))
print("样本真实:", " ".join(names))
# 清理
_TEMP_INJECT.clear(); clear_cache(); DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear()
