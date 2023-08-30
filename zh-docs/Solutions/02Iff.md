```lean
import GlimpseOfLean.Library.Basic
```

# 影响

## 使用蕴含

Lean使用符号`→`来表示蕴含，而不是`⇒`，因为它将`P → Q`的证明视为一个将任何`P`的证明送到`Q`的证明的函数（如果您看不到`→`和`⇒`之间的区别，请增大字体大小）。

例如，给定一个实数`a`，引理`sq_pos_of_pos`断言 `0 < a → 0 < a^2`，因此下面的证明将"函数"`sq_pos_of_pos`应用于假设`ha`。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < a^2 := by {
  exact sq_pos_of_pos ha
}
```

上述证明是一种直接证明：我们已经知道`0 < a`，并将此事实输入到蕴含中。
我们还可以使用`apply`策略进行逆向推理。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  apply sq_pos_of_pos -- 由于`sq_pos_of_pos`，只需证明`0 < a^2`
  apply sq_pos_of_pos -- 由于`sq_pos_of_pos`，只需证明`0 < a`
  exact ha -- 这正是我们的假设`ha`。
}
```

尝试使用引理`add_pos: 0 < x → 0 < y → 0 < x + y`完成下一个练习。
请注意，在应用`add_pos`之后，您将有两个目标，您需要逐个证明它们。

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

您还可以使用正向推理给出证明，使用`have`策略。
为了宣布一个中间语句，我们使用：

  `have my_name : my_statement`

这将触发一个新的目标：证明该语句。证明需要以一个中心点 `·`（使用`\.`输入）开头，并且应该进行缩进。
完成证明后，该语句将在名称 `my_name` 下可用。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  have h2 : 0 < a^2      -- 我们将 `0 < a^2` 声明为一个子目标
  · apply sq_pos_of_pos  -- 我们开始证明子目标
    exact ha             -- 这一行缩进，因此是子目标的一部分证明
  exact sq_pos_of_pos h2 -- 我们完成了子目标，现在我们使用它证明主目标。
}
```
```
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

为了证明蕴含关系，我们需要假设前提并证明结论。
这可以使用`intro`策略来完成。上面的练习实际上是在证明蕴含关系`a > 0 → (a^2)^2 > 0`，但是我们已经为前提引入了变量。

```lean
example (a : ℝ) : a > 0 → b > 0 → a + b > 0 := by {
  intro ha hb -- 可以在这里选择任何名称
  exact add_pos ha hb
}
```

现在证明以下简单的命题逻辑陈述。
请注意，`p → q → r`表示`p → (q → r)`。

```lean
example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by {
  -- sorry
  intro h1 h2 h3
  apply h2 h3
  exact h1 h3
  -- sorry
}
```

# 等价关系

## 使用等价关系重写陈述

在之前的文件中，我们看到了如何使用相等关系进行重写。
数学陈述中类似的操作是使用等价关系进行重写。这也是使用`rw`策略完成的。
Lean使用`↔`来表示等价关系，而不是`⇔`（如果you不能看到区别，请增大字体大小）。

在接下来的练习中，我们将使用引理：

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`

```lean
example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by {
  rw [← sub_nonneg]
  have key : (c + b) - (c + a) = b - a -- 在这里我们引入一个名为key的中间语句
  · ring   -- 通过在·后面证明它
  rw [key] -- 现在我们可以使用`key`。这个`rw`使用了一个等式结果，而不是等价关系
  rw [sub_nonneg] -- 并切换回等价的命题 a ≤ b ↔ a ≤ b
}
```

让我们证明一个变体。

```lean
example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by {
  -- sorry
  rw [← sub_nonneg]
  ring
  rw [sub_nonneg]
  -- sorry
}
```
```
上述引理已经在数学库中，名称为 `add_le_add_iff_right`：

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

这可以理解为："`add_le_add_iff_right`是一个函数，它将一个实数`c`作为输入，并输出一个证明`a + c ≤ b + c ↔ a ≤ b`"。下面是一个使用该引理的示例。

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by {
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by { rw [add_le_add_iff_right b] ; exact ha  }
}
```

## 将等价关系视为一对蕴含关系

在上面证明的第二行有点愚蠢：我们使用语句重写将目标简化为我们的假设`ha`，但我们更自然地将等价关系视为双向蕴含关系。我们可以通过`h.1: P→ Q` 和 `h.2: Q → P` 来访问等价关系`h: P ↔ Q` 的两个蕴含关系。这使得我们可以将上面的证明重写为：

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by {
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha
}
```

让我们使用`add_le_add_iff_left a: a + b ≤ a + c ↔ b ≤ c` 进行变体。

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by {
  -- sorry
  calc
    a = a + 0 := by ring
    _ ≤ a + b := by exact (add_le_add_iff_left a).2 hb
  -- sorry
}
```

## 证明等价关系

为了证明等价关系，可以使用 `rw` 直到目标是逻辑恒等式`P ↔ P`，就像等式一样。

也可以分别证明两个蕴含关系使用 `constructor`策略

下面是一个例子。

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
}
```

您可以在此练习中自行尝试。

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

这是学习处理蕴含关系和等价关系的文件的结束。您学到了以下策略：
* `intro`
* `apply`
* `have`
* `constructor`
