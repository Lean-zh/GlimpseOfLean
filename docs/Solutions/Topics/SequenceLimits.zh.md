```lean
import GlimpseOfLean.Library.Basic

namespace Topics

```

在这个文件中，我们操作实数序列极限的基本定义。mathlib 有更加通用的极限定义，但在这里我们想要练习使用前面文件中涉及的逻辑运算符和关系。

这个文件中有很多练习，如果遇到困难，不要犹豫去查看解答文件夹，那里还会有其他练习。

在开始之前，让我们确保 Lean 不需要太多帮助就能证明从已知等式和不等式线性推导出的等式或不等式。这是线性算术策略 `linarith` 的工作。

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

```

让我们使用 `linarith` 来证明一些练习。

```lean
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  -- sorry
  linarith
  -- sorry

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  -- sorry
  linarith
  -- sorry

```

序列 `u` 是从 `ℕ` 到 `ℝ` 的函数，因此 Lean 表示为 `u : ℕ → ℝ`
我们将使用的定义是：

- "u 趋向于 l" 的定义

```lean
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

```

注意使用了 `∀ ε > 0, _`，这是 `∀ ε, ε > 0 → _ ` 的简写。

特别地，像 `h : ∀ ε > 0, _` 这样的陈述可以通过以下方式特化到给定的 `ε₀`：
  `specialize h ε₀ hε₀`
其中 `hε₀` 是 `ε₀ > 0` 的证明。

另外注意，无论何时 Lean 期望某个证明项，我们都可以使用关键字 `by` 开始策略模式证明。例如，如果局部上下文包含：

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

那么我们可以使用以下方式将 h 特化到实数 δ/2：
  `specialize h (δ/2) (by linarith)`
其中 `by linarith` 将提供 Lean 期望的 `δ/2 > 0` 的证明。

如果 u 是值为 l 的常数序列，那么 u 趋向于 l。
提示：`simp` 可以将 `|l - l|` 重写为 `0`

```lean
example (h : ∀ n, u n = l) : seq_limit u l := by
  -- sorry
  intros ε ε_pos
  use 0
  intros n _
  rw [h]
  simp
  linarith
  -- sorry


```

关于用户界面的小备注：你可能已经注意到在前面的例子中，编辑器在 `example` 这个词后显示了一个有些虚幻的 `{u l}`。这个文本实际上不在 Lean 文件中，也不能编辑。它被显示为一个提示，表明 Lean 推断我们想要处理某些 `u` 和 `l`。`u` 应该是一个序列而 `l` 是一个实数这个事实是被推断出来的，因为宣告的结论是 `seq_limit u l`。

上述段落的简短版本是，你大多可以忽略这些虚幻的指示，相信你的常识即 `u` 是一个序列，`l` 是一个极限。

在处理绝对值时，我们将使用以下引理：

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

我们还将使用三角不等式的变形：

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
或
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
或带撇号的版本：
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`

```lean
-- 假设 `l > 0`。那么 `u` 趋向于 `l` 意味着对于足够大的 `n`，`u n ≥ l/2`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by
  -- sorry
  rcases h (l/2) (by linarith) with ⟨N, hN⟩
  use N
  intros n hn
  specialize hN n hn
  rw [abs_le] at hN
  linarith
  -- sorry


```

在处理 max 时，你可以使用：

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

让我们看一个例子。

```lean
-- 如果 `u` 趋向于 `l` 并且 `v` 趋向于 `l'`，那么 `u+v` 趋向于 `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)
  -- omit
```

  -- 不使用 `calc` 的替代证明
  simp
  have : |u n + v n - (l + l')| = |(u n - l) + (v n - l')|
  · ring
  rw [this]
  trans |u n - l| + |v n - l'|
  apply abs_add
  linarith [fact₁, fact₂]

```lean
  -- omit
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith


```

让我们做一些类似的事情：夹逼定理。
在这个例子中，使用 `specialize` 策略（在文件 `03Forall.lean` 中介绍）会有帮助，这样 `linarith` 策略就可以从假设中拾取相关文件。

```lean
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by
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
  -- 这里 `linarith` 可以完成，但在纸上我们会写
  calc
    -ε ≤ u n - l := by linarith
     _ ≤ v n - l := by linarith
  calc
    v n - l ≤ w n - l := by linarith
          _ ≤ ε := by linarith
  -- sorry



```

在下一个练习中，我们将使用：

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

回想一下，我们在这个文件的开头列出了三角不等式的三种变形。

```lean
-- 序列最多承认一个极限。你将能在下面的练习中使用这个引理。
lemma unique_limit : seq_limit u l → seq_limit u l' → l = l' := by
  -- sorry
  intros hl hl'
  apply eq_of_abs_sub_le_all
  intros ε ε_pos
  rcases hl (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hl' (ε/2) (by linarith) with ⟨N', hN'⟩
  specialize hN _ (le_max_left N N')
  specialize hN' _ (le_max_right N N')
  calc
    |l - l'| ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply abs_sub_le
           _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
           _ ≤ ε := by linarith
  -- sorry



```

现在让我们练习在证明之前解读定义。

```lean
def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by
  -- sorry
  intros ε ε_pos
  rcases h with ⟨inf_M, sup_M_ep⟩
  rcases sup_M_ep ε ε_pos with ⟨n₀, hn₀⟩
  use n₀
  intros n hn
  rw [abs_le]
  specialize inf_M n
  specialize h' n₀ n hn
  constructor
  · linarith
  · linarith
  -- sorry

```

现在我们来玩子序列。

我们将使用的新定义是 `φ : ℕ → ℕ` 是一个抽取函数，如果它是（严格）递增的。

```lean
def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

```

在下面，`φ` 始终表示从 `ℕ` 到 `ℕ` 的函数。

下一个引理通过简单的归纳来证明，但我们在这个教程中没有见过归纳法。如果你做过自然数游戏，那么你可以删除下面的证明并尝试重建它。

- 抽取函数大于恒等函数

```lean
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])


```

在练习中，我们使用 `∃ n ≥ N, ...`，这是 `∃ n, n ≥ N ∧ ...` 的简写。

- 抽取函数对于任意大的输入取任意大的值。

```lean
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  -- sorry
  intro h N N'
  use max N N'
  constructor
  apply le_max_right
  calc
    N ≤ max N N' := by apply le_max_left
    _ ≤ φ (max N N') := by apply id_le_extraction' h
  -- sorry

```

实数 `a` 是序列 `u` 的聚点，如果 `u` 有一个子序列收敛到 `a`。

```lean
def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

```

- 如果 `a` 是 `u` 的聚点，那么对于任意大的输入，存在 `u` 的值任意接近 `a`。

```lean
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  -- sorry
  intro hyp ε ε_pos N
  rcases hyp with ⟨φ, φ_extr, hφ⟩
  rcases hφ ε ε_pos with ⟨N', hN'⟩
  rcases extraction_ge φ_extr N N' with ⟨q, hq, hq'⟩
  exact ⟨φ q, hq', hN' _ hq⟩
  -- sorry


```

- 如果 `u` 趋向于 `l`，那么它的子序列趋向于 `l`。

```lean
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by
  -- sorry
  intro ε ε_pos
  rcases h ε ε_pos with ⟨N, hN⟩
  use N
  intro n hn
  apply hN
  calc
    N ≤ n := hn
    _ ≤ φ n := id_le_extraction' hφ n
  -- sorry

```

- 如果 `u` 趋向于 `l`，那么它的所有聚点都等于 `l`。

```lean
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by
  -- sorry
  rcases ha with ⟨φ, φ_extr, lim_u_φ⟩
  have lim_u_φ' : seq_limit (u ∘ φ) l := subseq_tendsto_of_tendsto' hl φ_extr
  exact unique_limit lim_u_φ lim_u_φ'
  -- sorry

```

- 柯西序列

```lean
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by
  -- sorry
  intro hyp
  rcases hyp with ⟨l, hl⟩
  intro ε ε_pos
  rcases hl (ε / 2) (by positivity) with ⟨N, hN⟩
  use N
  intro p q hp hq
  calc
    |u p - u q| = |u p - l + (l - u q)| := by ring_nf
    _ ≤ |u p - l| + |l - u q| := by apply abs_add
    _ = |u p - l| + |u q - l| := by rw [abs_sub_comm (u q) l]
    _ ≤ ε := by linarith [hN p hp, hN q hq]
  -- sorry

```

在下一个练习中，你可以重用：
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε

```lean
example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  -- sorry
  intro ε ε_pos
  rcases hu (ε / 2) (by positivity) with ⟨N, hN⟩
  use N
  have clef : ∃ N' ≥ N, |u N' - l| ≤ ε / 2 := by
    apply near_cluster hl (ε / 2) (by positivity)
  rcases clef with ⟨N', h⟩
  rcases h with ⟨hNN', hN'⟩
  intro n hn
  calc
    |u n - l| = |u n - u N' + (u N' - l)| := by ring_nf
    _ ≤ |u n - u N'| + |u N' - l| := by apply abs_add
    _ ≤ ε := by linarith [hN n N' hn hNN', hN']
  -- sorry

```