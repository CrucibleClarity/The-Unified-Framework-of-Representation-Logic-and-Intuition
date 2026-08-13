"""EXP-61h 平衡重跑: c0/c1 严格等量交替, 排除样本偏斜."""
import torch, json, random
from tokenizer import api
from tokenizer.token_index import inject_temp, clear_cache, _TEMP_INJECT
from tokenizer.maintain import core
from tokenizer._register import DERIVE_REGISTRY, DERIVE_BY_NAME, load_derive
from train import train_seq
from train.data import vocab
from lab import run_exp

# 注入
src = core.load_all()[api.eid_by_name("logical_and")]
defn = src.get("definition")
rows = [{"eid":"D:9001","name":"logical_and_c0","dtype":"bool","definition":defn},
        {"eid":"D:9002","name":"logical_and_c1","dtype":"bool","definition":defn}]
inject_temp("C", rows)
DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear(); load_derive(); clear_cache(); core._ALL_CACHE = None

# 构建 + 严格交替替换 (c0/c1 完全等量)
from lab import synth_core
cfg = json.load(open("docs/paper_data/configs/exp61g_infix_only.json"))
train, _, _ = synth_core.compose_samples(samples=cfg["synth"]["samples"], seed=0)
op_eid = api.eid_by_name("logical_and")
# 统计原 and 出现次数, 交替分配 c0/c1
and_positions = [(si, i) for si, s in enumerate(train) for i, e in enumerate(s["seq"]) if e == op_eid]
cnt = [0, 0]
for k, (si, i) in enumerate(and_positions):
    c = "D:9001" if k % 2 == 0 else "D:9002"
    train[si]["seq"][i] = c
    cnt[0 if c == "D:9001" else 1] += 1
print(f"严格交替: c0={cnt[0]} c1={cnt[1]}")

res = train_seq(train, epochs=15, dim=64, num_layers=2, seed=0, token="exp61h_bal", archive_dir=None)
m = res["model"]
print(f"train acc={res['acc']:.3f}")

# 评估单 clone
from lab.judge import judge_sequence
_T = api.role_token("truth"); TRUE, FALSE = _T
C0, C1 = "D:9001", "D:9002"
def mk(a, op, b, truth):
    return judge_sequence([TRUE if a else FALSE, op, TRUE if b else FALSE], truth)
def judge(seqs):
    ss = [{"seq": s, "valid": 1} for s in seqs]
    return run_exp._judge_eval(m, ss)[0]
seqs_c0 = [mk(a, C0, b, a and b) for a in (True,False) for b in (True,False)]
seqs_c1 = [mk(a, C1, b, a and b) for a in (True,False) for b in (True,False)]
print(f"只用 c0: {judge(seqs_c0):.3f} | 只用 c1: {judge(seqs_c1):.3f}")
torch.save(m.state_dict(), "/tmp/opencode/exp61h_bal_model.pt")
_TEMP_INJECT.clear(); clear_cache(); DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear()
print("平衡版完成")
