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
  have "cat [] [] = []" by (simp only: cateq1)
  then show "cat [] [] = []" by (simp)
next
  fix xs::"'a list" and x::'a
  assume HI: "cat xs [] = xs"
  have "cat (x#xs) [] = x # cat xs []" by (simp only: cateq2)
  have "x # cat xs [] = x # xs" by (simp only: HI)
  then show "cat (x#xs) [] = x # xs" by (simp)
qed


lemma l3: "\<forall>ys :: 'a list . reverso (cat xs ys) = cat (reverso ys) (reverso xs)"
  proof (induction xs)
    show "\<forall>ys :: 'a list . reverso (cat [] ys) = cat (reverso ys) (reverso [])"
    proof (intro allI)
      fix ys :: "'a list"
      have "reverso (cat [] ys) = reverso ys " by (simp only: cateq1)
      also have "... = cat (reverso ys) [] " by (simp only: l2)
      also have "... = cat (reverso ys) (reverso [])" by (simp only: reveq1)
      finally show "reverso (cat [] ys) = cat (reverso ys) (reverso [])" by (simp)
    qed
  next
    fix xs :: "'a list" and x::'a
    assume HI: "\<forall> ys :: 'a list . reverso (cat xs ys) = cat (reverso ys) (reverso xs)"
    show "\<forall>ys :: 'a list . reverso (cat (x#xs) ys) = cat (reverso ys) (reverso (x#xs))"
    proof (intro allI)
      fix ys :: "'a list"
      have "reverso (cat (x#xs) ys) = reverso (x#(cat xs ys)) " by (simp only: cateq2)
      also have "... = cat (reverso (cat xs ys)) [x]" by (simp only: reveq2)
      also have "... = cat (cat (reverso ys) (reverso xs)) [x]" by (simp only: HI)
      also have "... = cat (reverso ys) (cat (reverso xs) [x])" by (simp only: l1)
      also have "... = cat (reverso ys) (reverso (x#xs))" by (simp only: reveq2)
      finally show "reverso (cat (x#xs) ys) = cat (reverso ys) (reverso (x#xs))" by (simp)
    qed
  qed

theorem t1: "reverso (reverso xs) = xs"
  proof (induction xs)
    have "reverso (reverso []) = reverso []" by (simp only: reveq1)
    also have "reverso [] = []" by (simp only: reveq1)
    then show "reverso (reverso []) = []" by (simp)
  next
    fix xs :: "'a list" and x::'a
    assume HI: "reverso (reverso xs) = xs"
    have "reverso (reverso (x#xs)) = reverso (cat (reverso xs) [x])" by (simp only: reveq2)
    also have "... = cat (reverso [x]) (reverso (reverso xs))" by (simp only: l3)
    also have "... = cat (reverso (x#[])) xs" by (simp only: HI) (* transf. [x] \<rightarrow> x#[] nesse passo *)
    also have "... = cat (cat (reverso []) [x]) xs" by (simp only: reveq2)
    also have "... = cat (cat [] [x]) xs" by (simp only: reveq1)
    also have "... = cat (x#[]) xs" by (simp only: cateq1) (* transf. [x] \<rightarrow> x#[] nesse passo *)
    also have "... = x # (cat [] xs)" by (simp only: cateq2)
    also have "... = x # xs" by (simp only: cateq1)
    finally show "reverso (reverso (x#xs)) = x # xs" by (simp)
  qed
end