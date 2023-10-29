```lean
import GlimpseOfLean.Library.Basic
```

# 蕴含关系

## 使用蕴含关系

Lean 使用符号 `→` 代表蕴含关系，而不使用 `⇒`，因为它将 `P → Q` 的证明看作一个函数，该函数将任何 `P` 的证明转为 `Q` 的证明（如果你看不清楚 → 和 ⇒ 的区别，可以增大字体大小）。

例如，给定一个实数 `a`，引理 `sq_pos_of_pos` 声明了 `0 < a → 0 < a^2` 之间的关系，所以下面的证明应用了 "函数" `sq_pos_of_pos` 在假设 `ha` 上。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < a^2 := by {
  exact sq_pos_of_pos ha
}
```

以上的证明是一个直接证明：我们已经知道 `0 < a` 并且我们将这个事实带入到了蕴含式中。
我们也可以使用 `apply` 策略进行反向推理。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a^2`
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a`
  exact ha -- this is exactly our assumption `ha`.
}
```

尝试使用引理 `add_pos : 0 < x → 0 < y → 0 < x + y` 完成下一个练习。
注意，当你 `apply add_pos` 之后，你将会有两个目标，你需要一一证明它们。

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by {
  -- sorry
  apply add_pos
  apply sq_pos_of_pos
  exact ha
  apply sq_pos_of_pos
  exact hb
  -- sorry
}
```

你也可以使用 `have` 策略进行正向推理证明。 
当我们需要声明一个中间声明时，我们使用：

`have my_name : my_statement`

这将触发一个新目标的出现：证明该声明。证明需要从一个中心点 `·` (使用 `\.` 来输入)开始，并且应该进行缩进。
在证明完成后，该声明将在 `my_name` 名下可用。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  have h2 : 0 < a^2      -- we declare `0 < a^2` as a subgoal
  · apply sq_pos_of_pos  -- we start proving the subgoal
    exact ha             -- this line is indented, so part of the proof of the subgoal
  exact sq_pos_of_pos h2 -- we finished the subgoal, and now we prove the main goal using it.
}
```

现在用前向推理证明之前的相同引理。

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by {
  -- sorry
  have h2a : 0 < a^2
  · exact sq_pos_of_pos ha
  have h2b : 0 < b^2
  · exact sq_pos_of_pos hb
  exact add_pos h2a h2b
  -- sorry
}
```

## 证明蕴含关系

为了证明一个蕴含关系，我们需要假设前提并证明结论。
这是通过 `intro` 策略来完成的。在上面的练习中，我们实际上已经证明了蕴含关系 `a > 0 → (a^2)^2 > 0`，但是前提已经为我们引入了。

```lean
example (a : ℝ) : a > 0 → b > 0 → a + b > 0 := by {
  intro ha hb -- You can choose any names here
  exact add_pos ha hb
}
```

现在来证明下面的命题逻辑中的简单陈述。
请注意 `p → q → r` 意味着 `p → (q → r)`。

```lean
example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by {
  -- sorry
  intro h1 h2 h3
  apply h2 h3
  exact h1 h3
  -- sorry
}
```

# 等价

## 利用等价性重写陈述

在前一文件中，我们看到如何利用等式进行重写。
与数学陈述相对的操作是利用等价性重写。这也是用 `rw` 策略来完成的。
Lean 使用 `↔` 来表示等价性，而不是 `⇔`
（如果看不到差异，可以增大字体大小）。

在接下来的练习中，我们将使用如下的引理：

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`

```lean
example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by {
  rw [← sub_nonneg]
  have key : (c + b) - (c + a) = b - a -- Here we introduce an intermediate statement named key
  · ring   -- and prove it after a `·`
  rw [key] -- we can now use `key`. This `rw` uses an equality result, not an equivalence
  rw [sub_nonneg] -- and switch back to reach the tautology a ≤ b ↔ a ≤ b
}
```

让我们证明一个变体

```lean
example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by {
  -- sorry
  rw [← sub_nonneg]
  ring
  rw [sub_nonneg]
  -- sorry
}
```

上述引理已经包含在数学库中，名为 `add_le_add_iff_right`：

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

这可以读作：“`add_le_add_iff_right` 是一个函数，这个函数会接收一个实数 `c` 作为输入，并输出 `a + c ≤ b + c ↔ a ≤ b` 的证明”。这里有一个使用此引理的示例。

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by {
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by { rw [add_le_add_iff_right b] ; exact ha  }
}
```

## 使用等价性作为一对蕴涵式

在上述证明的第二行中，我们使用陈述重写将目标降低到我们的假设 `ha`，但更自然的是将等价性看作是一个双向蕴涵式。我们可以通过 `h : P ↔ Q` 分别访问等价性的两个蕴涵式 `h.1 : P → Q` 和 `h.2 : Q → P` 。这允许我们将上述证明重写为：

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by {
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha
}
```

让我们改为使用 `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` 这个变体。

以下是详细的翻译：

```
我们尝试使用代换法证明一个定理，这个定理陈述了 `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` ，在这之前我们先给出它的定义。

定义 `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` 采用以下形式：
如果当给定常数 `a` 时， `b ≤ c` ，那么就有 `a + b ≤ a + c` ，反之亦然。

注意到这个定理与我们在整数加法上看到的相似。在那里，我们已经知道如果 `b ≤ c` ，那么 `a + b ≤ a + c` （这是加法的单调性）。而且，如果 `a + b ≤ a + c` ，我们可以减去 `a` 来得到 `b ≤ c` 。

下面的定理使用同样的证明方法。

## 定理： `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` 

证明：

由于 `b ≤ c` ，我们可以使用加法的单调性得到 `a + b ≤ a + c` 。

通过减去 `a` ，我们得到 `b ≤ c` 。

在数学研究中，这个定理对于理解和证明加法性质是非常重要的。它告诉我们，我们可以凭借已知的加法属性来推断和证明未知的属性。
```

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by {
  -- sorry
  calc
    a = a + 0 := by ring
    _ ≤ a + b := by exact (add_le_add_iff_left a).2 hb
  -- sorry
}
```

## 证明等价性

为了证明等价性，你可以使用 `rw` 命令，直到目标变为 "P ↔ P" 这样的重言式，这与处理等式的方法相同。

你也可以分别使用 `constructor` 策略来证明两个命题间的蕴含关系。

以下是一个例子。

```lean
example (a b : ℝ) : (a-b)*(a+b) = 0 ↔ a^2 = b^2 := by {
  constructor
  · intro h
    calc
      a ^ 2 = b^2 + (a - b) * (a + b)  := by ring
          _ = b^2 + 0                  := by rw [h]
          _ = b^2                      := by ring
  · intro h
    calc
      (a-b)*(a+b) = a^2 - b^2  := by ring
                _ = b^2 - b^2  := by rw [h]
                _ = 0          := by ring
  }
```

你可以在此练习中自己尝试。

```lean
example (a b : ℝ) : a = b ↔ b - a = 0 := by {
  -- sorry
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    calc
      a = b - (b - a) := by ring
      _ = b - 0       := by rw [h]
      _ = b           := by ring
  -- sorry
}
```

这是本文件的结尾，你已经学会如何处理蕴含和等价。你学习了以下策略：
* `intro`
* `apply`
* `have`
* `constructor`
