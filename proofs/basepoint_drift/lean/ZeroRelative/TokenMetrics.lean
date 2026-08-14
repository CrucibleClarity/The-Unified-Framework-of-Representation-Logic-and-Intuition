import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Formal.ZeroRelative.ComplexAxis

/-!
# token 度量体系: token 数量 / 承载信息量 / 推理速度

语言符号系统 = 有限简单图 (顶点 = token, 边 = 定义/引用)。三度量:
  * token 数量: 顶点数 (tokenCount)
  * 承载信息量: 塌缩 (直觉收敛) 后可分辨点数 (carryingInfo)
  * 推理速度: 任意 token 间最短路径总和 (totalPaths) / 均值 (avgDist)

规律 (塌缩投影工具的应用):
  * 信息不增: 塌缩后点数 ≤ 原点数
  * 每对 token 推理路径不增 (连通图): 商图距离 ≤ 原图距离
  * 总路径不增 (连通图)
  * 平均路径非单调 (诚实标注): 塌缩合并跨分量点, 平均可增
  * 捷径 (直觉直接连接) 不增距离: 加边 → 最短路径不增
-/

namespace ZeroRelative

/-- token 数量: 图中 token (顶点) 个数。 -/
def tokenCount (V : Type u) [Fintype V] : ℕ :=
  Fintype.card V

/-- 塌缩投影是满射 (每类有代表)。 -/
theorem collapseProj_surjective (S : Type u) (K : Set S) :
    Function.Surjective (ComplexAxis.collapseProj S K) := by
  intro q
  rcases Quot.exists_rep q with ⟨a, ha⟩
  exact ⟨a, ha⟩

/-- 商空间是有限类型 (由 V 有限)。 -/
noncomputable instance collapseFinite (S : Type u) (K : Set S) [Fintype S] :
    Finite (ComplexAxis.collapseSpace S K) :=
  Finite.of_surjective (ComplexAxis.collapseProj S K) (collapseProj_surjective S K)

noncomputable instance collapseFintype (S : Type u) (K : Set S) [Fintype S] :
    Fintype (ComplexAxis.collapseSpace S K) :=
  Fintype.ofFinite (ComplexAxis.collapseSpace S K)

/-- 承载信息量 (塌缩后可分辨 token 点数): 商图顶点数。 -/
noncomputable def carryingInfo (V : Type u) [Fintype V] (K : Set V) : ℕ :=
  Fintype.card (ComplexAxis.collapseSpace V K)

/-- 推理速度 (总路径): 任意 token 对最短路径总和。 -/
noncomputable def totalPaths (G : SimpleGraph V) [Fintype V] : ℕ :=
  Finset.univ.sum fun u : V => Finset.univ.sum fun v : V => G.dist u v

/-- 推理速度 (均值): 平均最短路径 = totalPaths / |V|^2。 -/
noncomputable def avgDist (G : SimpleGraph V) [Fintype V] : ℚ :=
  (totalPaths G : ℚ) / ((Fintype.card V : ℕ) ^ 2 : ℚ)

/-- 商图: 塌缩 K 后 (类不同, 且存在代表相邻)。 -/
def collapseGraph (G : SimpleGraph V) (K : Set V) : SimpleGraph (ComplexAxis.collapseSpace V K) where
  Adj x y := x ≠ y ∧ ∃ u v : V, G.Adj u v ∧ ComplexAxis.collapseProj V K u = x ∧ ComplexAxis.collapseProj V K v = y
  symm := {
    symm := by
      intro x y h
      rcases h with ⟨hne, u, v, huv, hu, hv⟩
      exact ⟨hne.symm, v, u, G.symm.symm u v huv, hv, hu⟩
  }
  loopless := {
    irrefl := by
      intro x h
      exact h.1 rfl
  }

/-- walk 压缩: 原图 walk 投影为商图 walk (同类步删除, 长度不增)。 -/
noncomputable def collapseWalk (G : SimpleGraph V) (K : Set V) {u v : V}
    (p : G.Walk u v) :
    (collapseGraph G K).Walk (ComplexAxis.collapseProj V K u) (ComplexAxis.collapseProj V K v) :=
  match p with
  | .nil => .nil
  | @SimpleGraph.Walk.cons _ _ u v w h p =>
      haveI := Classical.decEq (ComplexAxis.collapseSpace V K)
      dite (ComplexAxis.collapseProj V K u = ComplexAxis.collapseProj V K v)
        (fun heq => by
          rw [heq]
          exact collapseWalk G K p)
        (fun heq => .cons ⟨heq, u, v, h, rfl, rfl⟩ (collapseWalk G K p))

/-- 压缩后长度不增。 -/
theorem collapseWalk_length_le (G : SimpleGraph V) (K : Set V) {u v : V}
    (p : G.Walk u v) : (collapseWalk G K p).length ≤ p.length := by
  classical
  induction p with
  | nil => simp [collapseWalk]
  | cons h p ih =>
      unfold collapseWalk
      simp only [SimpleGraph.Walk.length_cons]
      by_cases heq : ComplexAxis.collapseProj V K u = ComplexAxis.collapseProj V K v
      · rw [if_pos heq]
        simp only [SimpleGraph.Walk.length_cons]
        exact Nat.le_trans ih (Nat.le_add_right _ 1)
      · rw [if_neg heq]
        simp only [SimpleGraph.Walk.length_cons]
        exact Nat.succ_le_succ ih

/-- 每对 token 推理路径不增 (任意 walk 版本): 商图距离 ≤ 原 walk 长度。 -/
theorem collapse_dist_le_of_walk (G : SimpleGraph V) (K : Set V) (p : G.Walk u v) :
    (collapseGraph G K).dist (ComplexAxis.collapseProj V K u) (ComplexAxis.collapseProj V K v) ≤ p.length := by
  exact le_trans (SimpleGraph.dist_le (collapseWalk G K p)) (collapseWalk_length_le G K p)

/-- 每对 token 推理路径不增 (连通图): 商图距离 ≤ 原图距离。 -/
theorem collapse_dist_le (G : SimpleGraph V) (K : Set V) (hG : G.Connected) (u v : V) :
    (collapseGraph G K).dist (ComplexAxis.collapseProj V K u) (ComplexAxis.collapseProj V K v) ≤ G.dist u v := by
  rcases hG.exists_walk_length_eq_dist u v with ⟨p, hp⟩
  rw [← hp]
  exact collapse_dist_le_of_walk G K p

/-- 信息不增: 塌缩后 token 点数 ≤ 原点数。 -/
theorem collapse_info_le (V : Type u) [Fintype V] (K : Set V) :
    carryingInfo V K ≤ tokenCount V := by
  exact Fintype.card_le_of_surjective (ComplexAxis.collapseProj V K) (collapseProj_surjective V K)

/-- 商类代表选择是单射 (不同类选不同代表)。 -/
theorem out_injective (S : Type u) (K : Set S) :
    Function.Injective (fun q : ComplexAxis.collapseSpace S K => Quot.out q) := by
  intro q1 q2 h
  calc
    q1 = ComplexAxis.collapseProj S K (Quot.out q1) := (Quot.out_eq q1).symm
    _ = ComplexAxis.collapseProj S K (Quot.out q2) := by
          exact congrArg (ComplexAxis.collapseProj S K) h
    _ = q2 := Quot.out_eq q2

/-- 注入求和界: 对单射 f, 像上的求和 ≤ 全空间求和 (非负值)。 -/
theorem sum_le_sum_of_injective {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (g : β → ℕ) [Fintype α] [Fintype β] :
    Finset.univ.sum (fun a : α => g (f a)) ≤ Finset.univ.sum (fun b : β => g b) := by
  classical
  rw [← Finset.sum_image (f := g) (s := (Finset.univ : Finset α)) (g := f)]
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (f := g)
      (s := Finset.univ.image f) (t := Finset.univ)
      (fun b hb => by simp) (fun b hb hn => Nat.zero_le _)
  · intro a ha b hb hab
    exact hf hab

/-- 总路径不增 (连通图): 塌缩后推理开销不增。 -/
theorem collapse_totalPaths_le (G : SimpleGraph V) [Fintype V] (K : Set V) (hG : G.Connected) :
    totalPaths (collapseGraph G K) ≤ totalPaths G := by
  calc
    totalPaths (collapseGraph G K) =
        Finset.univ.sum (fun q1 : ComplexAxis.collapseSpace V K =>
          Finset.univ.sum (fun q2 : ComplexAxis.collapseSpace V K => (collapseGraph G K).dist q1 q2)) :=
      rfl
    _ ≤ Finset.univ.sum (fun q1 : ComplexAxis.collapseSpace V K =>
          Finset.univ.sum (fun q2 : ComplexAxis.collapseSpace V K => G.dist (Quot.out q1) (Quot.out q2))) := by
          apply Finset.sum_le_sum
          intro q1 hq1
          apply Finset.sum_le_sum
          intro q2 hq2
          calc
            (collapseGraph G K).dist q1 q2
                = (collapseGraph G K).dist
                    (ComplexAxis.collapseProj V K (Quot.out q1))
                    (ComplexAxis.collapseProj V K (Quot.out q2)) := by
                    congr 1
                    · exact (Quot.out_eq q1).symm
                    · exact (Quot.out_eq q2).symm
            _ ≤ G.dist (Quot.out q1) (Quot.out q2) :=
              collapse_dist_le G K hG (Quot.out q1) (Quot.out q2)
    _ ≤ Finset.univ.sum (fun q1 : ComplexAxis.collapseSpace V K =>
          Finset.univ.sum (fun v : V => G.dist (Quot.out q1) v)) := by
          apply Finset.sum_le_sum
          intro q1 hq1
          exact sum_le_sum_of_injective (fun q2 : ComplexAxis.collapseSpace V K => Quot.out q2)
            (out_injective V K) (G.dist (Quot.out q1))
    _ ≤ Finset.univ.sum (fun u : V => Finset.univ.sum (fun v : V => G.dist u v)) := by
          exact sum_le_sum_of_injective (fun q1 : ComplexAxis.collapseSpace V K => Quot.out q1)
            (out_injective V K) (fun u : V => Finset.univ.sum (fun v : V => G.dist u v))

/-- 权衡律 (核心): 塌缩 (直觉收敛) 后 — 信息不增 且 推理路径不增。 -/
theorem info_speed_tradeoff (G : SimpleGraph V) [Fintype V] (K : Set V) (hG : G.Connected) :
    carryingInfo V K ≤ tokenCount V ∧
      totalPaths (collapseGraph G K) ≤ totalPaths G ∧
      ∀ u v : V,
        (collapseGraph G K).dist (ComplexAxis.collapseProj V K u) (ComplexAxis.collapseProj V K v) ≤ G.dist u v := by
  exact ⟨collapse_info_le V K, collapse_totalPaths_le G K hG, fun u v => collapse_dist_le G K hG u v⟩

/-- 捷径 (直觉直接连接) 不增推理路径: 加边后距离 ≤ 原距离。 -/
theorem shortcut_dist_le (G G' : SimpleGraph V) (hGG' : G ≤ G') (hG : G.Connected) (u v : V) :
    G'.dist u v ≤ G.dist u v := by
  rcases hG.exists_walk_length_eq_dist u v with ⟨p, hp⟩
  rw [← hp]
  let hom : G →g G' :=
    { toFun := (fun x : V => x),
      map_rel' := by
        intro x y h
        exact hGG' h }
  calc
    G'.dist u v = G'.dist (hom u) (hom v) := by simp [hom]
    _ ≤ (SimpleGraph.Walk.map hom p).length := SimpleGraph.dist_le (SimpleGraph.Walk.map hom p)
    _ = p.length := SimpleGraph.Walk.length_map hom p

end ZeroRelative
