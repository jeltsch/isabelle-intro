section \<open>Start\<close>

theory Isabelle_Intro
  imports Main
begin

section \<open>Predefined Inductive Type\<close>

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

section \<open>Custom Inductive Type\<close>

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

section \<open>Computation Induction\<close>

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse _ [] = []" |
  "intersperse _ [x] = [x]" |
  "intersperse y (x # xs) = x # y # intersperse y xs"

value "intersperse (0 :: nat) [1]"
value "intersperse (0 :: nat) [1, 2]"
value "intersperse (0 :: nat) [1, 2, 3]"

lemma "intersperse (0 :: nat) [1, 2, 3] = [1, 0, 2, 0, 3]" by simp

lemma intersperse_map: "map f (intersperse y xs) = intersperse (f y) (map f xs)"
proof (induction xs rule: intersperse.induct)
  case 1
  show ?case by simp
next
  case 2
  show ?case by simp
next
  case 3
  then show ?case by simp
qed

lemma "map f (intersperse y xs) = intersperse (f y) (map f xs)" \<comment> \<open>now proved more explicitly\<close>
proof (induction xs rule: intersperse.induct)
  fix y
  show "map f (intersperse y []) = intersperse (f y) (map f [])"
    by simp
next
  fix y and x
  show "map f (intersperse y [x]) = intersperse (f y) (map f [x])"
    by simp
next
  fix y and x\<^sub>1 and x\<^sub>2 and xs
  assume "map f (intersperse y (x\<^sub>2 # xs)) = intersperse (f y) (map f (x\<^sub>2 # xs))"
  then show "map f (intersperse y (x\<^sub>1 # x\<^sub>2 # xs)) = intersperse (f y) (map f (x\<^sub>1 # x\<^sub>2 # xs))"
    by simp
qed

section \<open>Inductive Predicate\<close>

inductive closure :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" for r where
  refl: "closure r x x" |
  step: "\<lbrakk> r x y; closure r y z \<rbrakk> \<Longrightarrow> closure r x z"

inductive closure' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" for r where
  refl': "closure' r x x" |
  step': "\<lbrakk> closure' r x y; r y z \<rbrakk> \<Longrightarrow> closure' r x z"

lemma closure_implies_closure': "closure r x y \<Longrightarrow> closure' r x y"
proof (induction rule: closure.induct)
  case refl
  show ?case by (fact refl')
next
  case (step x y z)
  from `closure' r y z` and `r x y` show "closure' r x z"
  proof (induction rule: closure'.induct)
    case refl'
    then show ?case by (blast intro: closure'.intros)
  next
    case step'
    then show ?case by (blast intro: closure'.step')
  qed
qed

section \<open>End\<close>

end
