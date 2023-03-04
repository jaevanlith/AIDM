include "globals.mzn";

% Length of schedule
int: w = 7;
% Number of employees
int: groups;
%Number of work shifts
int: numShifts;
% Demand
array[1..numShifts,1..w] of int: demand;
% Max & min length per shift
array[1..numShifts] of int: minShift;
array[1..numShifts] of int: maxShift;
% Min & max length of blocks of assignment: no shift
int: minOff;
int: maxOff;
% Min & max length of blocks of assignment: working shift
int: minOn;
int: maxOn;
% Forbidden sequences of shifts
set of int: shifts = 0..numShifts;
array[1..numShifts] of set of shifts: forbidden;
% Forbidden sequences of shifts of length 3
array[int,1..3] of int: forbidden3;

% Schedule
array[1..groups,1..w] of var 0..numShifts: S;
var 0..(w-1) : o; % offset

% == Constraints == %
array[1..numShifts] of int: shifts_array = [j | j in 1..numShifts];

% meet demand; cumulative global constaint?
constraint forall(d1, d2 in 1..w where (d2 + o - 1) mod (w) + 1 = d1)(global_cardinality(col(S,d1),shifts_array) == col(demand,d2)) :: domain;
constraint forall(d1, d2 in 1..w where (d2 + o - 1) mod (w) + 1 = d1)(count(col(S, d1), 0) == groups - sum(col(demand,d2))); % optimization: redundant constraint

% predicate blockConstraint_min(int: s, int: min) = 
% forall (i in 1..groups) (
%     forall(j in 1..(w-1) where S[i, j + 1] == s /\ S[i, j] != s) (
%           count([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in 0..(min - 1)
%             where ((j + k) div w) + i <= groups], s) == min
%           )
%       );
      
predicate blockConstraint_min(int: s, int: min) = 
forall (i in 1..groups) (
    forall(j in 1..(w-1) where S[i, j + 1] == s /\ S[i, j] != s) (
          (((j + (min - 1)) div w) + i <= groups) /\ all_equal([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in 0..(min - 1)])
          )
      ); % optimized
                                              
predicate blockConstraint_max(int: s, int: min, int: max) = 
forall (i in 1..groups) (
    forall(j in 1..(w-1) where S[i, j + 1] == s /\ S[i, j] != s) (
          count([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in min..max
            where ((j + k) div w) + i <= groups], s) <= max - min
          )
      );

% shift blocks
constraint forall (s in shifts_array) (blockConstraint_min(s, minShift[s])); % minima          
constraint forall (s in shifts_array) (blockConstraint_max(s, minShift[s], maxShift[s])); % maxima

% off blocks
constraint blockConstraint_min(0, minOff); % minima     
constraint blockConstraint_max(0, minOff, maxOff); % minima

% working blocks
constraint forall (i in 1..groups) (
              forall(j in 1..(w-1) where S[i, j + 1] != 0 /\ S[i, j] == 0) (
                    among([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in 0..(minOn - 1) 
                      where ((j + k) div w) + i <= groups], 1..numShifts) == minOn
                    )
                ); % minima
                
constraint forall (i in 1..groups) (
              forall(j in 1..(w-1) where S[i, j + 1] != 0 /\ S[i, j] == 0) (
                    among([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in minOn..maxOn 
                      where ((j + k) div w) + i <= groups], 1..numShifts) <= maxOn - minOn 
                    )
                ); % maxima
                
                
% consider first element
constraint (count([S[(k div w) + 1,(k mod w) + 1] | k in 0..(minOff - 1) where (k div w) + 1 <= groups], 0) == minOff);
constraint (count([S[(k div w) + 1,(k mod w) + 1] | k in minOff..maxOff where (k div w) + 1 <= groups], 0) <= maxOff - minOff);

constraint forall (i in 2..groups where S[i, 1] == 0) (S[i - 1, w] == S[i, 1] \/ count([S[(k div w) + i,(k mod w) + 1] | k in 0..(minOff - 1) where (k div w) + i <= groups], 0) == minOff);
constraint forall (i in 2..groups where S[i, 1] == 0) (S[i - 1, w] == S[i, 1] \/ count([S[(k div w) + i,(k mod w) + 1] | k in minOff..maxOff where (k div w) + i <= groups], 0) <= maxOff - minOff);

constraint forall (i in 2..groups where S[i, 1] != 0) (forall (s in 1..numShifts where s == S[i, 1]) (S[i - 1, w] == s \/ count([S[(k div w) + i,(k mod w) + 1] | k in 0..(minShift[s] - 1) where (k div w) + i <= groups], s) == minShift[s]));
constraint forall (i in 2..groups where S[i, 1] != 0) (forall (s in 1..numShifts where s == S[i, 1]) (S[i - 1, w] == s \/ count([S[(k div w) + i,(k mod w) + 1] | k in minShift[s]..maxShift[s] where (k div w) + i <= groups], s) <= maxShift[s] - minShift[s]));

constraint forall (i in 2..groups where S[i, 1] != 0) (S[i - 1, w] != 0 \/ among([S[(k div w) + i,(k mod w) + 1] | k in 0..(minOn - 1) where (k div w) + i <= groups], 1..numShifts) = minOn) ;
constraint forall (i in 2..groups where S[i, 1] != 0) (S[i - 1, w] != 0 \/ among([S[(k div w) + i,(k mod w) + 1] | k in minOn..maxOn where (k div w) + i <= groups], 1..numShifts) <= maxOn - minOn);

% symmetry breaking (cyclic nature)                    
constraint S[1, 1] = 0;
constraint S[groups, w] != 0; % block contraints assume that the last and first elements are not equal!!

predicate equalArray3(array[1..3] of int: arr1, array[1..3] of var int: arr2) = forall (k in 1..3) (arr1[k] == arr2[k]);

constraint forall(i in 1..groups) (forall (j in 1..w where S[i, j] != 0) (not member(forbidden[S[i,j]], S[((j) div (w) + (i - 1)) mod (groups) + 1, (j) mod (w) + 1])));
constraint forall(i in 1..groups) (forall (j in 1..w where S[i, j] != 0) (forall(f in 1..(length(forbidden3) div 3)) ( not equalArray3 (row(forbidden3, f), [S[((j + k - 1) div (w) + (i - 1)) mod (groups) + 1, (j + k - 1) mod (w) + 1] | k in 0..2]))));
                
% symmetry breaking (offset)
constraint member(2..maxOff, o) \/ o == (w - (max([d | d in 1..w where sum(col(demand, d mod (w) + 1)) < sum(col(demand, d))]) - 1)) mod w;
                
% maximize free weekends
var int : sat = (5 + o) mod (w) + 1;
var int : sun = (6 + o) mod (w) + 1;
var int : f1 = count([S[i, sat] | i in 1..groups], 0) + count([S[i, sun] | i in 1..groups], 0);

% free weekend distance
array[int] of var int : f_full = [S[i, sat] + S[i, sun] | i in 1..groups];
array[int] of var opt int : dist1 = [(j - 1) * (j - 1) | i, j in 1..groups where (f_full[(i + j - 1) mod (groups) + 1] = 0 /\ f_full[i] = 0)];
array[int] of var opt int : dist2 = [groups * groups | i in 1..groups where f_full[i] != 0];

% solve :: int_search([S[i, sun] | i in 1..groups], first_fail, indomain_min) :: int_search([S[i, sat] | i in 1..groups], first_fail, indomain_min) :: int_search([o], first_fail, indomain) maximize f1 - sum(dist1) - sum(dist2);

solve :: int_search([S[i, sun] | i in 1..groups], first_fail, indomain_min) :: int_search([S[i, sat] | i in 1..groups], first_fail, indomain_min) :: int_search([o], first_fail, indomain) maximize sum([1 | i in 1..groups where f_full[i] == 0]);

output ["[", concat([(if fix(S[((i + o - 1) div (w)) mod (groups) + 1, (i + o - 1) mod (w) + 1]) == 0 then "-," else concat([show(S[((i + o - 1) div (w)) mod (groups) + 1, (i + o - 1) mod (w) + 1]), ","]) endif) | i in 1..(groups * w - 1)] ++ [(if fix(S[((i + o - 1) div (w)) mod (groups) + 1, (i + o - 1) mod (w) + 1]) == 0 then "-" else concat([show(S[((i + o - 1) div (w)) mod (groups) + 1, (i + o - 1) mod (w) + 1])]) endif) | i in (groups * w)..(groups * w)]), "]\n",

show(sum([1 | i in 1..groups where f_full[i] == 0]))]