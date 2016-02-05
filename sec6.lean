import standard

section sec6_1

inductive weekday : Type :=
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday

print weekday
print prefix weekday

inductive shingichi : Type :=
| shin
| gi

open shingichi

definition katsu (b1 b2 : shingichi) : shingichi :=
shingichi.cases_on b1 b2 gi

variables b1 b2 : shingichi

eval katsu b1 b2
eval katsu shin shin
eval katsu shin gi
eval katsu gi shin
eval katsu gi gi
eval katsu shin b1
eval katsu gi b1
eval katsu b1 gi

end sec6_1
