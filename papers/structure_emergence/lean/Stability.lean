import Mathlib.Tactic
import TokenRelative.Observe

/-!
# TokenRelative.Stability — 结构稳定性定理

用户推演 (2026-08-14) 的形式化:

  T1 信息由结构承载, 结构不同 → 信息不同 (承载 = 单射)
  T2 涌现信息与涌现过程是两个信息 (产物 ≠ 过程)

推演:
  1. 4 个全同 e, 只允许完美匹配 (互锁), 全连接 (无孤立) → 唯一稳定结构
  2. 唯一结构 → 无结构差异 → 承载不了 (不同的) 信息
  3. 增加 2 个 e (6 个): 完美匹配同构类仍唯一 → 结构仍唯一 → 仍承载不了
-/

namespace TokenRelative.Stability

open TokenRelative.Observe

-- ============================================================
-- T1: 信息由结构承载 (结构不同 → 信息不同)
-- ============================================================

/--
T1: 信息由结构承载 — 承载是"结构 → 信息"的单射函数:
结构不同 → 信息不同 (否则两个不同结构承载同一信息, 信息无法由结构区分)。
-/
def CarriesInjective {S I : Type} (info : S → I) : Prop :=
  Function.Injective info

-- ============================================================
-- T2: 涌现信息与涌现过程是两个信息
-- ============================================================

/--
T2: 从无中涌现一个信息 (产物), 与从无到这个信息的过程 (箭头),
是两个不同的信息。
-/
structure TwoInfo (I : Type) where
  product : I        -- 涌现产物 (信息)
  process : I        -- 涌现过程 (箭头承载)
  distinct : product ≠ process   -- 两者不同

-- ============================================================
-- 4 个 e: 完美匹配唯一稳定结构
-- ============================================================

/-- 4 顶点完美匹配: 每个 e 恰好激活一条边 (度 = 1)。 -/
abbrev IsPerfectMatching4 (s : State) : Prop :=
  ∀ v : V, degree s v = 1

/-- 4 顶点完美匹配的全体 (枚举: 3 个)。 -/
def perfectMatchings4 : List State :=
  allStates.filter (fun s => decide (IsPerfectMatching4 s))

/-- 4 顶点完美匹配恰好是这 3 个 (canonList 顺序, 全同下归 1 类)。 -/
theorem perfectMatchings4_eq :
    perfectMatchings4 =
      [[(0, 3), (1, 2)], [(0, 2), (1, 3)], [(0, 1), (2, 3)]] := by
  native_decide

/-- 定理 1: 4 e 完美匹配 3 个 (标签下), 同构类 1 个。 -/
theorem stableStructure4_unique :
    (computeReps.filter (fun s => decide (IsPerfectMatching4 s))).length = 1 := by
  native_decide

-- ============================================================
-- 推论 2: 唯一稳定结构 → 承载不了 (不同的) 信息
-- ============================================================

/--
推论 2: 完美匹配两两同构 (结构唯一) → 若同构结构承载相同信息,
则所有稳定结构承载同一个信息 — 无信息差异。
-/
theorem no_info_difference
    {I : Type} (info : State → I)
    (h_same : ∀ {s t : State}, Isomorphic s t → info s = info t) :
    ∀ s ∈ perfectMatchings4, ∀ t ∈ perfectMatchings4, info s = info t := by
  intro s hs t ht
  have hs_cases : s = [(0, 3), (1, 2)] ∨ s = [(0, 2), (1, 3)] ∨ s = [(0, 1), (2, 3)] := by
    simpa [perfectMatchings4_eq] using hs
  have ht_cases : t = [(0, 3), (1, 2)] ∨ t = [(0, 2), (1, 3)] ∨ t = [(0, 1), (2, 3)] := by
    simpa [perfectMatchings4_eq] using ht
  rcases hs_cases with rfl | rfl | rfl
  all_goals
    rcases ht_cases with rfl | rfl | rfl
  all_goals
    apply h_same
    native_decide

-- ============================================================
-- 6 个 e: 增加 2 个 e — 完美匹配同构类仍唯一
-- ============================================================

/-- 6 顶点 (Fin 6)。 -/
abbrev V6 := Fin 6

/-- 6 顶点 15 条规范候选边。 -/
def canonList6 : List (V6 × V6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
   (1, 2), (1, 3), (1, 4), (1, 5),
   (2, 3), (2, 4), (2, 5),
   (3, 4), (3, 5),
   (4, 5)]

/-- 6 顶点完美匹配的全体 (15 个)。 -/
def perfectMatchings6 : List (List (V6 × V6)) :=
  [[(0, 1), (2, 3), (4, 5)], [(0, 1), (2, 4), (3, 5)], [(0, 1), (2, 5), (3, 4)],
   [(0, 2), (1, 3), (4, 5)], [(0, 2), (1, 4), (3, 5)], [(0, 2), (1, 5), (3, 4)],
   [(0, 3), (1, 2), (4, 5)], [(0, 3), (1, 4), (2, 5)], [(0, 3), (1, 5), (2, 4)],
   [(0, 4), (1, 2), (3, 5)], [(0, 4), (1, 3), (2, 5)], [(0, 4), (1, 5), (2, 3)],
   [(0, 5), (1, 2), (3, 4)], [(0, 5), (1, 3), (2, 4)], [(0, 5), (1, 4), (2, 3)]]

/-- 6 顶点置换 (720 个, 泛型排列生成)。 -/
def perms6 : List (List V6) :=
  permutations [0, 1, 2, 3, 4, 5]

/-- 6 顶点边排序 (Lex)。 -/
def lePair6 (a b : V6 × V6) : Bool :=
  if a.1 < b.1 then true
  else if b.1 < a.1 then false
  else a.2 ≤ b.2

/-- 6 顶点边规范化 (无序对排序)。 -/
def normPair6 (e : V6 × V6) : V6 × V6 :=
  if e.1 ≤ e.2 then e else (e.2, e.1)

/-- 插入排序 (6 顶点边)。 -/
def insertSorted6 (e : V6 × V6) : List (V6 × V6) → List (V6 × V6)
  | [] => [e]
  | x :: xs => if lePair6 e x then e :: x :: xs else x :: insertSorted6 e xs

/-- 状态排序 (6 顶点)。 -/
def sortState6' (s : List (V6 × V6)) : List (V6 × V6) :=
  s.foldr insertSorted6 []

/-- 置换作用 (6 顶点)。 -/
def applyPerm6 (p : List V6) (s : List (V6 × V6)) : List (V6 × V6) :=
  sortState6' (s.map (fun e =>
    normPair6 (p.getD e.1.val (0 : V6), p.getD e.2.val (0 : V6))))

/-- 6 顶点同构。 -/
abbrev Isomorphic6 (s t : List (V6 × V6)) : Prop :=
  ∃ p ∈ perms6, applyPerm6 p s = t

/-- 定理 2: 6 e 完美匹配 15 个 (标签下), 两两同构 — 同构类仍唯一。 -/
theorem perfectMatching6_unique :
    perfectMatchings6.length = 15 ∧
    (perfectMatchings6.all (fun s =>
      perfectMatchings6.all (fun t => decide (Isomorphic6 s t)))) = true := by
  native_decide

-- ============================================================
-- 破缺 1 个 e: 承载两个结构
-- ============================================================

/--
破缺态: 4 个 e 中 1 个破缺 (退出互锁), 其伙伴失配 —
恰 1 对互锁 (2 个度 1) + 2 个未配对 (度 0), 每 e 至多一条边。
-/
abbrev IsBroken4 (s : State) : Prop :=
  (∀ v : V, degree s v ≤ 1) ∧
  ((List.finRange 4).filter (fun v => decide (degree s v = 1))).length = 2

/--
定理 3: 破缺 1 个 e 产生两种结构 —
  结构 1: 完美匹配 (2 对, 度 1,1,1,1)
  结构 2: 破缺 (1 对 + 2 未配对, 度 1,1,0,0)
  两者同构类各 1, 并集 2 类 — 可承载两个不同的信息。
-/
theorem broken1_yields_two_structures :
    (computeReps.filter (fun s => decide (IsPerfectMatching4 s ∨ IsBroken4 s))).length = 2 := by
  native_decide

/-- 定理 4: 必须破缺 — 完美匹配 (不破缺) 只有 1 类; 破缺 1 个 e 贡献第 2 类。 -/
theorem must_broken_for_two :
    (computeReps.filter (fun s => decide (IsPerfectMatching4 s))).length = 1 ∧
    (computeReps.filter (fun s => decide (IsBroken4 s))).length = 1 := by
  native_decide

/-- 信息函数: 结构 → 信息 (完美匹配 = true, 其余 = false)。 -/
def classInfo (s : State) : Bool :=
  decide (IsPerfectMatching4 s)

/--
定理 5: 两种结构可承载两个不同的信息 —
存在信息函数, 对完美匹配与破缺态给出不同信息 (T1: 结构不同 → 信息不同)。
-/
theorem two_info_carried :
    ∃ info : State → Bool,
      ∃ s t : State, IsPerfectMatching4 s ∧ IsBroken4 t ∧ info s ≠ info t := by
  refine ⟨classInfo, [(0, 1), (2, 3)], [(0, 1)], ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

end TokenRelative.Stability
