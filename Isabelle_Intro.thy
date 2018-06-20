theory Isabelle_Intro
  imports Main
begin

fun sum_up_to :: "nat \<Rightarrow> nat" where
  "sum_up_to 0 = 0" |
  "sum_up_to (Suc n) = sum_up_to n + Suc n"

lemma gauss: "sum_up_to n = n * (n + 1) div 2"
proof (induction n)
  case 0
  show ?case by simp
next
  case Suc
  then show ?case by simp
qed

datatype 'a tree =
  Leaf |
  Branch 'a "('a tree)" "('a tree)"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  mirror_leaf: "mirror Leaf = Leaf" |
  mirror_branch: "mirror (Branch x t\<^sub>1 t\<^sub>2) = Branch x (mirror t\<^sub>2) (mirror t\<^sub>1)"

lemma double_mirror: "mirror (mirror t) = t"
proof (induction t)
  case Leaf
  show ?case by simp
next
  case (Branch x t\<^sub>1 t\<^sub>2)
  have "mirror (mirror (Branch x t\<^sub>1 t\<^sub>2)) = mirror (Branch x (mirror t\<^sub>2) (mirror t\<^sub>1))"
    by (rule arg_cong [OF mirror_branch])
  also have "\<dots> = Branch x (mirror (mirror t\<^sub>1)) (mirror (mirror t\<^sub>2))"
    by (rule mirror_branch)
  also have "\<dots> = Branch x t\<^sub>1 t\<^sub>2"
    by (simp add: Branch.IH)
  finally show ?case .
qed

end
