theory T1_2026_2
  imports Main
begin

primrec cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
cateq1: "cat [] ys = ys" |
cateq2: "cat (x#xs) ys = x#cat xs ys"

primrec reverso :: "'a list \<Rightarrow> 'a list" where
reveq1: "reverso [] = []" |
reveq2: "reverso (x#xs) = cat (reverso xs) [x]"

lemma l1: "\<forall>ys zs :: 'a list . cat xs (cat ys zs) = cat (cat xs ys) zs"
proof (induction xs)
  show "\<forall>ys zs :: 'a list . cat [] (cat ys zs) = cat (cat [] ys) zs"
  proof (intro allI)
    fix ys zs :: "'a list"
    have "cat [] (cat ys zs) = cat ys zs" by (simp only: cateq1)
    also have "... = cat (cat [] ys) zs" by (simp only: cateq1)
    finally show "cat [] (cat ys zs) = cat (cat [] ys) zs" by (simp)
  qed
next
  fix xs::"'a list" and x::'a
  assume HI:"\<forall> ys zs :: 'a list . cat xs (cat ys zs) = cat (cat xs ys) zs"
  show "\<forall>ys zs :: 'a list . cat (x#xs) (cat ys zs) = cat (cat (x#xs) ys) zs"
  proof (rule allI, rule allI)
    fix ys zs :: "'a list"
    have "cat (x#xs) (cat ys zs) = x # cat xs (cat ys zs)" by (simp only: cateq2)
    also have "... = x # cat (cat xs ys) zs" by (simp only: HI)
    also have "... = cat (x # cat xs ys) zs" by (simp only: cateq2)
    also have "... = cat (cat (x#xs) ys) zs" by (simp only: cateq2)
    finally show "cat (x#xs) (cat ys zs) = cat (cat (x#xs) ys) zs" by (simp)
  qed
qed

lemma l2: "cat xs [] = xs"
proof(induction xs)
  case Nil
  have "cat [] [] = []" by (rule cateq1)
  then show ?case .
next
  case (Cons x xs)
  assume IH: "cat xs [] = xs" 
  have "cat (x#xs) [] = x # cat xs []" by (rule cateq2)
  have "x # cat xs [] = x # xs" by (subst IH)
  finally show ?case .
qed


lemma l3: "\<forall>ys :: 'a list . reverso (cat xs ys) = cat (reverso ys) (reverso xs)"
  sorry

theorem t1: "reverso (reverso xs) = xs"
  sorry

end