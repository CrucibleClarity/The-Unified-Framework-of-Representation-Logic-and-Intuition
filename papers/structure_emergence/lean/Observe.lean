import Mathlib.Tactic
import Mathlib.Data.List.FinRange

/-!
# TokenRelative.Observe — 互锁状态观测工具

目标 (用户 2026-08-14): 无视类型化的互锁观测 —
  4 个 E (同一类型, 无角色标签: 不区分对象/方向/结构/信息),
  观测两两互锁的所有状态, 按等价分类, 看有几种、是否等价。

建模 (纯 List 计算, 零 noncomputable):
  V = Fin 4         四个无类型 E (仅编号, 零类型标签)
  边 = (a, b) 规范对 (a < b)   互锁 = 无向边集
  状态 = 激活边列表 (List (V × V))
  等价 = 图同构 (顶点置换下互变) — "无类型" = 标签可任意置换
-/

namespace TokenRelative.Observe

-- ============================================================
-- 1. 基础: 4 个无类型 E
-- ============================================================

/-- 4 个无类型 E: 仅编号 0,1,2,3, 无任何角色标签。 -/
abbrev V := Fin 4

/-- 6 条可能互锁边 (规范无序对 a < b)。 -/
def canonList : List (V × V) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

-- ============================================================
-- 2. 互锁状态 (纯计算枚举)
-- ============================================================

/-- 互锁状态: 激活边列表。 -/
abbrev State := List (V × V)

/-- 全部子集 (递归枚举, 2^6 = 64)。 -/
def subsets : List (V × V) → List State
  | [] => [[]]
  | e :: es =>
      let rest := subsets es
      rest.map (fun s => s) ++ rest.map (fun s => e :: s)

/-- 全部 64 个互锁状态。 -/
def allStates : List State :=
  subsets canonList

-- ============================================================
-- 3. 等价: 图同构 (无类型 = 标签可任意置换)
-- ============================================================

/-- 元素插入到列表的所有位置 (全排列生成辅助)。 -/
def insertEverywhere {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (fun l => y :: l)

/-- 全排列 (纯计算)。 -/
def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (permutations xs) >>= fun l => insertEverywhere x l

/-- Fin 4 的全部 24 个置换 (查表函数形式)。 -/
def perms4 : List (List V) :=
  permutations [0, 1, 2, 3]

/-- 置换查表: p[i]。 -/
def permAt (p : List V) (i : V) : V :=
  p.getD i.val (0 : V)

/-- 边规范化: 无序对按 a < b 排序。 -/
def normPair (e : V × V) : V × V :=
  if e.1 ≤ e.2 then e else (e.2, e.1)

/-- 边全序 (Lex: 先比 fst 再比 snd)。 -/
def lePair (a b : V × V) : Bool :=
  if a.1 < b.1 then true
  else if b.1 < a.1 then false
  else a.2 ≤ b.2

/-- 插入排序 (纯计算)。 -/
def insertSorted (e : V × V) : State → State
  | [] => [e]
  | x :: xs => if lePair e x then e :: x :: xs else x :: insertSorted e xs

/-- 状态排序 (规范化, 消除边顺序差异 — List 相等是顺序敏感的)。 -/
def sortState (s : State) : State :=
  s.foldr insertSorted []

/-- 置换作用在边上。 -/
def permEdge (p : List V) (e : V × V) : V × V :=
  normPair (permAt p e.1, permAt p e.2)

/-- 置换作用在状态上 (结果排序, 使相等与边顺序无关)。 -/
def applyPerm (p : List V) (s : State) : State :=
  sortState (s.map (permEdge p))

/-- 同构等价: 存在置换使两状态互变。 -/
def Isomorphic (s t : State) : Prop :=
  ∃ p ∈ perms4, applyPerm p s = t

/-- 同构可判定 (有限置换列表枚举)。 -/
instance : DecidableRel Isomorphic := by
  intro s t
  unfold Isomorphic
  infer_instance

/-- 可计算代表列表: 按 allStates 顺序, 保留第一个不与已选同构的状态。 -/
def computeReps : List State :=
  allStates.foldl (fun acc t =>
    if acc.any (fun s => Isomorphic s t) then acc else acc ++ [t]) []

-- ============================================================
-- 4. 观测: 性质
-- ============================================================

/-- 顶点度: 状态 s 中 v 的互锁边数。 -/
def degree (s : State) (v : V) : Nat :=
  (s.filter (fun e => e.1 = v ∨ e.2 = v)).length

/-- 奇度顶点数。 -/
def oddCount (s : State) : Nat :=
  ((List.finRange 4).filter (fun v : V => degree s v % 2 = 1)).length

/-- 可一笔画 (欧拉路径): 奇度顶点数 = 0 或 2。 -/
abbrev Eulerian (s : State) : Prop :=
  oddCount s = 0 ∨ oddCount s = 2

-- ============================================================
-- 5. 观测定理
-- ============================================================

/-- 观测 1: 互锁状态总数 = 64。 -/
theorem state_count : allStates.length = 64 := by
  native_decide

/-- 观测 2: 同构等价类数 = 11 (4 顶点未标记图分类, 经典结果)。 -/
theorem class_count : computeReps.length = 11 := by
  native_decide

/-- 观测 3: 等价类不是一种 — 64 状态 ≠ 1 类, 而是 11 类。 -/
theorem not_single_class : computeReps.length ≠ 1 := by
  norm_num [class_count]

/-- 观测 4: 可一笔画的同构类数 (欧拉图 + 半欧拉图, 奇度顶点 0 或 2)。 -/
theorem eulerian_class_count :
    (computeReps.filter (fun s => decide (Eulerian s))).length = 8 := by
  native_decide

/-- 观测 5: 不可一笔画的同构类数 = 11 - 8 = 3
    (2 边不相邻 / 3 边星形 / 6 边 K4 — 全传递不能一笔画)。 -/
theorem non_eulerian_class_count :
    (computeReps.filter (fun s => decide (¬ Eulerian s))).length = 3 := by
  native_decide

/-- 观测 6: 全传递 (K4, 6 边全互锁) 不能一笔画 — 4 个奇度顶点。 -/
theorem K4_not_eulerian :
    ¬ Eulerian [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] := by
  native_decide

/-- 观测 7: K4 的 4 个顶点全是奇度 (度 3)。 -/
theorem K4_all_odd :
    (List.finRange 4).all (fun v : V => decide (degree
      [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] v % 2 = 1)) = true := by
  native_decide

end TokenRelative.Observe
