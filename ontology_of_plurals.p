%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%An ontology of composite, collectives, and pluralities.

%Implemented by Daniele Porello on the basis of the ontology
%developed by Claudio Masolo and Laure Vieu
%with contributions by Stefano Borgo and Roberta Ferrario.

%May 2020

%Proved consistent with Darwin 1.4.4
%Using the Hets environment https://github.com/spechub/Hets

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Taxonomy
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_taxonomy, axiom, (![X]: (ob(X) | time(X)) <=> pt(X))).

fof(ax_taxonomy_disj, axiom, (~?[X]: (ob(X) & time(X)))).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Mereology of objects
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_part_objects, axiom, (![X,Y]: (part(X,Y) => (ob(X) & ob(Y))))).

fof(ax_part_rifl, axiom, (![X]: (ob(X) => part(X,X)))).

fof(ax_part_antisymm, axiom, (![X,Y]: ((part(X,Y) & part(Y,X)) => (Y=X)))).

fof(ax_part_trans, axiom, (![X,Y,Z]: ((part(X,Y) & part(Y,Z)) => part(X,Z)))).

fof(ax_part_overlapping, axiom, (![X,Y]: (overlap(X,Y) <=> ?[Z]:(part(Z,X) & part(Z,Y))))).

fof(ax_part_underlapping, axiom, (![X,Y]: (underlap(X,Y) <=> ?[Z]:(part(X,Z) & part(Y,Z))))).

fof(ax_part_strong_supp, axiom, (![X,Y]: ((ob(X) & ob(Y) & ~part(Y,X)) => ?[Z]:(part(Z,Y) & ~overlap(Z,X))))).

fof(ax_part_proper_part, axiom, (![X,Y]: (properPart(Y,X) <=> (part(Y,X) & ~part(X,Y))))).

fof(ax_part_sum, axiom, (![Z,X,Y]: (sum(Z,X,Y) <=> ![W]:((overlap(W,Z) <=> (overlap(W,X) | overlap(W,Y))))))).

fof(ax_part_sum_existence, axiom, (![X,Y]: (underlap(X,Y) => (?[Z]:(![W]:((overlap(W,Z) <=> (overlap(W,X) | overlap(W,Y))))))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Atoms and atomic parts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Atoms (instances of time are atoms)

fof(ax_atom, axiom, (![X]: (atom(X) <=> ~?[Y]:(properPart(Y,X))))).

%Atomicity

fof(ax_atomicity, axiom, (![X]: (ob(X) => ?[Y]: (atom(Y) & part(Y,X))))).

%Atomic part

fof(ax_atomic_part, axiom, (![X,Y]: (atomicPart(X,Y) <=> (part(X,Y) & atom(X))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Existence, wholly exists, and parthood.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_taxonomy, axiom, (![X,T]: (exists(X,T) => (ob(X) & time(T))))).

%objects exist at at least one time:

fof(ax_objects_exist, axiom, (![X]: (ob(X) => ?[T]: (time(T) & exists(X,T))))).

%Wholly exist at time t:

fof(ax_wholly_exist, axiom, ((![X,T]: (existsW(X,T) <=> (exists(X,T) & ![Y]: (part(Y,X) => exists(Y,T))))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Pluralities, composites, and collectives
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Constitutions, const1 and const2

%Pluralities are mereological sums.

%const1(X,Y,T) : at time T, the object (a composite) X is constituted(1) by the plurality Y.

%const2(X,Y,T) :  at time T, the object (a collective) X is constituted(2) by the plurality Y.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Ob(X) added, as times are atom, otherwise they could be constituted:

fof(ax_const1, axiom, (![X,Y,T]: (const1(X,Y,T) => (exists(X,T) & existsW(Y,T) & ob(X) & ob(Y) & atom(X) & ~atom(Y) & time(T))))).

fof(ax_const2, axiom, (![X,Y,T]: (const2(X,Y,T) => (exists(X,T) & existsW(Y,T) & ob(X) & ob(Y) & atom(X) & ~atom(Y) & time(T))))).

%Constituted objects are always constituted:

fof(ax_const1_a10, axiom, (![X,T,T1]: ((exists(X,T) & exists(X,T1)) => (?[Y]: const1(X,Y,T) <=> ?[Y1]: const1(X,Y1,T1))))).

fof(ax_const2_a11, axiom, (![X,T,T1]: ((exists(X,T) & exists(X,T1)) => (?[Y]: const2(X,Y,T) <=> ?[Y1]: const2(X,Y1,T1))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Collectives, unicity of decomposition
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


fof(ax_const2_unicity_decomposition, axiom, (![X,Y,Z,T]: ((const2(X,Y,T) & const2(X,Z,T))  => (Y = Z)))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Composite, covering
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_const1_covering, axiom, (![X,Y,Z,T]: ((const1(X,Y,T) & const1(X,Z,T)) => ~(part(Y,Z) & ~(Y=Z))))).

%fof(ax_const1_covering, axiom, (![X,Y,Z,T]: ((const1(X,Y,T) & const1(X,Z,T)) => (~part(Y,Z) | (Y=Z))))).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Recursive decomposition
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_const1_recursive_decomposition, axiom, (![X,Y,Y1,Y2,A,Z,T]: ((const1(X,Y1,T) & atomicPart(A,Y1) & sum(Y1,Y,A) & (const1(A,Z,T) | const2(A,Z,T)) & sum(Y2,Y,Z)) => const1(X,Y2,T)))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Properties of members (const2) and components (const1)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_const1_overlap, axiom, (![X,Y,T]: ((const1(X,Y,T))  => (~overlap(X,Y))))).
fof(ax_const2_overlap, axiom, (![X,Y,T]: ((const2(X,Y,T))  => (~overlap(X,Y))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Composite (const 1) and collectives (const 2)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_composite, axiom, (![X]:(composite(X) <=> (![T]: exists(X,T) => ?[Y]:(const1(X,Y,T)))))).
fof(ax_collective, axiom, (![X]:(collective(X) <=> (![T]: exists(X,T) => ?[Y]:(const2(X,Y,T)))))).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Components of composite (const1) and members of collectives (const2)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_component, axiom, (![X,Y,T]: (component(X,Y,T) <=> (?[Z]: (const1(Y,Z,T) & atomicPart(X,Z)))))).

fof(ax_member, axiom, (![X,Y,T]: (member(X,Y,T) <=> (?[Z]: (const2(Y,Z,T) & atomicPart(X,Z)))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Component asymmetry (theorem)

%fof(ax_component_asymm, axiom, (![X,Y,T]: (component(X,Y,T) => ~component(Y,X,T)))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Member asymmetry

fof(ax_member_asymm, axiom, (![X,Y,T]: (member(X,Y,T) => ~(member(Y,X,T))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Subcollectives and subcomposite

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_sub_component, axiom, (![X,Y,T]: (subcomposite(X,Y,T) <=> (?[A,B]: (const1(X,A,T) & const1(Y,B,T) & part(A,B)))))).

fof(ax_sub_collective, axiom, (![X,Y,T]: (subcollective(X,Y,T) <=> (?[A,B]: (const2(X,A,T) & const2(Y,B,T) & part(A,B)))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Types of composite, collectives and pluralities
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%propF and propG: properties of pluralities
%propP : type of composites
%propQ : type of collectives


fof(ax_const1_property, axiom, (![X,Y,T]: (propF(X,T) & ~atomic(X) & existsW(X,T)) =>
                                ?[Y]: (propP(Y) & const1(Y,X,T) & ![T1]:(exists(Y,T1) => ?[X1]: (const1(Y,X1,T1) & propF(X1,T1)))))).

fof(ax_const2_property, axiom, (![X,Y,T]: (propG(X,T) & ~atomic(X) & existsW(X,T)) =>
                                ?[Y]: (propQ(Y) & const2(Y,X,T) & ![T1]:(exists(Y,T1) => ?[X1]: (const2(Y,X1,T1) & propG(X1,T1)))))).


fof(ax_const1_property2, axiom, (![Y]: (propP(Y) => ![T]: (exists(Y,T) & ?[X]: (const1(Y,X,T) & propF(X,T)))))).


fof(ax_const2_property2, axiom, (![Y]: (propQ(Y) => ![T]: (exists(Y,T) & ?[X]: (const2(Y,X,T) & propG(X,T)))))).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%TESTS AND THEOREMS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




%Test instances:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Test: const1 and const2

%fof(test_const12, axiom, (const1(a1,a1,t1))). %INCONSISTENT
%fof(test_const13, axiom, (const1(a1,b1,t1) & sum(b1,a1,c1))). %INCONSISTENT
%fof(test_const21, axiom, (const2(a1,b1,t1) & sum(b1,a1,c1))). %INCONSISTENT
%fof(test_const15, axiom, (const1(a2,b2,t2) & const1(a2,c2,t2) & ~(b2 = c2))). %CONSISTENT
%fof(test_const22, axiom, (const2(a5,b5,t5) & const2(a5,c5,t5) & ~(b5 = c5))). %INCONSISTENT
%fof(test_const16, axiom, (const1(a6,b6,t6) & const1(a6,c6,t6) & sum(b6,b61,b62) & sum(c6,c61,c62) & ~(b61 = c61) & ~(b62 = c62) & atom(b61) & atom(b62) & atom(c61) & atom(c62))). %CONSISTENT
%fof(test_const17, axiom, (const1(a7,b3,t3) & exists(a7,t4) & ~?[X]: (const1(a7,X,t4)) &  ~?[X1]: (const2(a7,X1,t4)))). %INCONSISTENT.
%fof(test_const2_1, axiom, (const2(a7,b3,t3) & const1(a7,b3,t3) & exists(a7,t4) & ~?[X]: (const1(a7,X,t4)))). %INCONSISTENT:  an object that is both a composite and collective is always both.


%Test: composites and collectives

%fof(test_members_intr, axiom, (((member(a,b,t) & member(b,c,t)) & ~member(a,c,t)))). %CONSISTENT
%fof(test_component_transitivity, axiom, (((ob(a) & ob(b) & component(a,b,t) & component(b,c,t)) & ~component(a,c,t)))). %INCONSISTENT


%Test: subcomposite and subcollectives

%fof(test_sub_composite, axiom, ((subcomposite(s11,s12,t)))). %CONSISTENT
%fof(test_sub_coll, axiom, ((subcollective(s12,s13,t)))). %CONSISTENT
%fof(test_sub_composite, axiom, ((subcomposite(s11,s12,t) & subcollective(s12,s13,t)))). %CONSISTENT
%fof(test_sub_coll, axiom, ((subcollective(s1,s2,t) & subcollective(s2,s3,t) & ~(subcollective(s1,s3,t))))).  %INCONSISTENT

%Test of theorems:

%fof(test_trans_memebr_component, axiom, ((member(s1,s2,t) & component(s2,s3,t) & ~(component(s1,s3,t))))).  %INCONSISTENT
%fof(test_component_asymm, axiom, ((component(s1,s2,t) & component(s2,s1,t) & ~(s1 = s2)))).%INCONSISTENT
%fof(test_comp_overlap, axiom, (((component(s,c,t)) & ~(?[Z] : ((~(overlap(Z,c)) & component(Z,c,t))))))). %INCONSISTENT
%fof(test_memb_overlap, axiom, (((member(s,c,t)) & ~(?[Z] : ((~(overlap(Z,c)) & member(Z,c,t))))))). %INCONSISTENT
%fof(test_collective_composite1, conjecture, (collective(s) & composite(s) & member(m,s,t) & ~(component(m,s,t)))). %INCONSISTENT
%fof(test_collective_composite2, conjecture, (collective(s) & composite(s) & component(m,s,t) & ~(member(m,s,t) | subcollective(m,s,t)))). %INCONSISTENT


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%THEOREMS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%Mereology:%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%if X has proper parts, then it is the sum of two things.

fof(cj_proper_parts_and_sums, conjecture, (![Y]: ((?[X]: (properPart(X,Y))) => (?[Y1,Y2]: (sum(Y,Y1,Y2)))))). %OK

%Non-atomic objects are sums:

fof(cj_atoms_and_sums, conjecture, (![X]: (~atom(X) => (?[Y1,Y2]: (sum(X,Y1,Y2)))))). %OK

%Theorems%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(ax_test_rec_decomposition1, conjecture, ((const1(x,y1,t) & sum(y1,y,a21) & atomicPart(a21,y1) & const1(a21,z,t) & sum(y2,y,z))  => const1(x,y2,t))). %OK

fof(ax_test_rec_decomposition2, conjecture, ((const1(x,y1,t) & sum(y1,y,a21) & atomicPart(a21,y1) & const2(a21,z,t) & sum(y2,y,z))  => const1(x,y2,t))). %OK

fof(th_test_irr_components, conjecture, ((![T,X]: (~component(X,X,T))))). %OK

fof(th_test_irr_members, conjecture, ((![T,X]: (~member(X,X,T))))). %OK.

fof(th_test_trans_components, conjecture, ((![X,Y,Z,T]: (component(X,Y,T) & component(Y,Z,T)) => component(X,Z,T)))). %OK

fof(th_test_trans_sub_collective, conjecture, ((![X,Y,Z,T]: ((subcollective(X,Y,T) & subcollective(Y,Z,T)) => subcollective(X,Z,T))))). %OK.

fof(th_test_trans_mix_member_component, conjecture, ((![X,Y,Z,T]: ((member(X,Y,T) & component(Y,Z,T)) => component(X,Z,T))))). %The prover fails, but see: test_trans_memebr_component

fof(th_component_asymm, conjecture, (((![X,Y,T]: ((component(X,Y,T) => ~(component(Y,X,T)))))))). %The prover fails but see: test_component_asymm

fof(th_test_comp_overlap, conjecture, ((![X,Y,T]: (component(X,Y,T) => ?[Z] : ((~(overlap(Z,X)) & component(Z,Y,T))))))). %The prover fails, but see: test_comp_overlap

fof(th_test_member_overlap, conjecture, ((![X,Y,T]: (member(X,Y,T) => ?[Z] : ((~(overlap(Z,X)) & member(Z,Y,T))))))). %The prover fails, but see: test_memb_overlap

fof(th_test_collective_composite1, conjecture, ((![X,Y,T]: ((collective(X) & composite(X) & member(Y,X,T))  => component(Y,X,T))))). %The prover fails, but see: test_collective_composite1

fof(th_test_collective_composite2, conjecture, ((![X,Y,T]: ((collective(X) & composite(X) & component(Y,X,T))  => (member(Y,X,T) | subcollective(Y,X,T)))))). %The prover fails, but see: test_collective_composite1
