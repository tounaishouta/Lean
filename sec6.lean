import standard

namespace sec6_1

inductive weekday : Type :=
| sunday    : weekday
| monday    : weekday
| tuesday   : weekday
| wednesday : weekday
| thursday  : weekday
| friday    : weekday
| saturday  : weekday

open weekday

definition next_day : weekday → weekday :=
weekday.rec monday tuesday wednesday thursday friday saturday sunday

definition day_after (n : ℕ) (d : weekday) : weekday :=
nat.rec_on n d (λ n' d', next_day d')

eval day_after 3 monday

end sec6_1
