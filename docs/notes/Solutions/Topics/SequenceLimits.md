```lean
import GlimpseOfLean.Library.Basic
```

在这个文件中，我们操作实数序列的极限的基本定义。
mathlib 中有一个更一般的极限定义，但在这里，我们想练习使用在之前的文件中涵盖的逻辑运算符和关系。

在我们开始之前，让我们确保 Lean 在证明从已知的等式和不等式线性推导出的等式或不等式时不需要太多帮助。这是线性算术策略的工作：`linarith`。

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith
```

让我们使用 `linarith` 来证明一些练习题。

```lean
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  -- sorry
  linarith
  -- sorry
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  -- sorry
  linarith
  -- sorry
}
```

一个序列 `u` 是从 `ℕ` 到 `ℝ` 的函数，因此 Lean 表示为 `u : ℕ → ℝ`。
我们将使用以下定义：

-- « u 趋向于 l » 的定义
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

注意到使用 `∀ ε > 0, _` 这个简写，它是 `∀ ε, ε > 0 → _` 的缩写。

特别地，对于形如 `h : ∀ ε > 0, _` 的语句，
可以通过 `specialize h ε₀ hε₀` 将其特化为给定的 `ε₀`，
其中 `hε₀` 是证明 `ε₀ > 0` 的证明。

还要注意，无论在何处，当 Lean 需要一些证明项时，我们都可以使用关键字 `by` 开始一个策略模式证明。
例如，如果局部上下文包含：

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

那么我们可以使用以下方式将 h 特化为实数 δ/2：
`specialize h (δ/2) (by linarith)`
其中 `by linarith` 将提供 Lean 所期望的 `δ/2 > 0` 的证明。

如果 u 是一个取值为 l 的常数函数，那么 u 趋向于 l。
```

```lean
example (h : ∀ n, u n = l) : seq_limit u l := by {
  -- sorry
  intros ε ε_pos
  use 0
  intros n _
  rw [h]
  simp
  linarith
  -- sorry
}
```

处理绝对值时，我们会使用以下引理：

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

我们还将使用三角不等式的变体之一：

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
或
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
或者其标记为 prime 的版本：
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`

```lean
-- 假设 `l > 0`。那么 `u` 趋向于 `l` 意味着对于足够大的 `n`，`u n ≥ l/2`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  -- sorry
  rcases h (l/2) (by linarith) with ⟨N, hN⟩
  use N
  intros n hn
  specialize hN n hn
  rw [abs_le] at hN
  linarith [hN]
  -- sorry
}
```

处理 max 函数时，你可以使用以下引理：

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

让我们看一个例子。

```lean
-- 如果 `u` 趋向于 `l` 并且 `v` 趋向于 `l'`，那么 `u+v` 趋向于 `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2
  · exact hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2
  · exact hN₂ n (by linarith)
  -- omit
}
```

```lean
-- altenative proof without using `calc`
  simp
  have : |u n + v n - (l + l')| = |(u n - l) + (v n - l')|
  · ring
  rw [this]
  trans |u n - l| + |v n - l'|
  apply abs_add
  linarith [fact₁, fact₂]

-- omit
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}
```

让我们尝试类似的方法：夹逼定理。

```lean
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  -- sorry
  intros ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  rcases hw ε ε_pos with ⟨N', hN'⟩
  use max N N'
  intros n hn
  rw [ge_max_iff] at hn
  specialize hN n (by linarith)
  specialize hN' n (by linarith)
  specialize h n
  specialize h' n
  rw [abs_le] at *
  constructor
  -- Here `linarith` can finish, but on paper we would write
  calc
    -ε ≤ u n - l := by linarith
     _ ≤ v n - l := by linarith
  calc
    v n - l ≤ w n - l := by linarith
          _ ≤ ε := by linarith
  -- sorry
}
```

在下一个练习中，我们将使用引理

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

回想一下，我们在本文件开头列出了三个三角不等式变体。

```lean
-- 序列的极限最多只有一个。你可以在以下练习中使用该引理。
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  -- sorry
  intros hl hl'
  apply eq_of_abs_sub_le_all
  intros ε ε_pos
  rcases hl (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hl' (ε/2) (by linarith) with ⟨N', hN'⟩
  calc
    |l - l'| ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply abs_sub_le
           _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
           _ ≤ ε := by linarith [hN _ (le_max_left N N'), hN' _ (le_max_right N N')]
  -- sorry
}
```

```lean
def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  -- sorry
  intros ε ε_pos
  rcases h with ⟨inf_M, sup_M_ep⟩
  rcases sup_M_ep ε ε_pos with ⟨n₀, hn₀⟩
  use n₀
  intros n hn
  rw [abs_le]
  constructor <;> linarith [inf_M n, h' n₀ n hn]
  -- sorry
}
```

现在我们来练习在证明之前解读定义。

```lean
def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}

lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  -- sorry
  intro h N N'
  use max N N'
  constructor
  apply le_max_right
  calc
    N ≤ max N N' := by apply le_max_left
    _ ≤ φ (max N N') := by apply id_le_extraction' h
  -- sorry
}

def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a
```

```lean
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  -- sorry
  intro hyp ε ε_pos N
  rcases hyp with ⟨φ, φ_extr, hφ⟩
  cases' hφ ε ε_pos with N' hN'
  rcases extraction_ge φ_extr N N' with ⟨q, hq, hq'⟩
  exact ⟨φ q, hq', hN' _ hq⟩
  -- sorry
}
```

如果 `a` 是 `u` 的一个聚点，那么对于任意大的输入，`u` 存在与 `a` 足够接近的值。

```lean
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  -- sorry
  intro ε ε_pos
  cases' h ε ε_pos with N hN
  use N
  intro n hn
  apply hN
  calc
    N ≤ n := hn
    _ ≤ φ n := id_le_extraction' hφ n
  -- sorry
}
```

如果 `u` 趋向于 `l`，那么它的子序列也趋向于 `l`。

```lean
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  -- sorry
  rcases ha with ⟨φ, φ_extr, lim_u_φ⟩
  have lim_u_φ' : seq_limit (u ∘ φ) l := subseq_tendsto_of_tendsto' hl φ_extr
  exact uniq_limit lim_u_φ lim_u_φ'
  -- sorry
}
```

如果 `u` 趋向于 `l`，那么它的所有聚点都等于 `l`。

```lean
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  -- sorry
  intro hyp
  cases' hyp with l hl
  intro ε ε_pos
  cases' hl (ε / 2) (by linarith) with N hN
  use N
  intro p q hp hq
  calc
    |u p - u q| = |u p - l + (l - u q)| := by ring_nf
    _ ≤ |u p - l| + |l - u q| := by apply abs_add
    _ = |u p - l| + |u q - l| := by rw [abs_sub_comm (u q) l]
    _ ≤ ε := by linarith [hN p hp, hN q hq]
  -- sorry
}
```

```lean
example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  -- sorry
  intro ε ε_pos
  cases' hu (ε / 2) (by linarith) with N hN
  use N
  have clef : ∃ N' ≥ N, |u N' - l| ≤ ε / 2
  apply near_cluster hl (ε / 2) (by linarith)
  cases' clef with N' h
  cases' h with hNN' hN'
  intro n hn
  calc
    |u n - l| = |u n - u N' + (u N' - l)| := by ring_nf
    _ ≤ |u n - u N'| + |u N' - l| := by apply abs_add
    _ ≤ ε := by linarith [hN n N' hn hNN', hN']
  -- sorry
```
在下一个练习中，你可以重用 `near_cluster` 引理：`cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε`
