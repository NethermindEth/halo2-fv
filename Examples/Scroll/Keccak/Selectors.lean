import Examples.Scroll.Keccak.Extraction

namespace Keccak

  namespace Selectors
    -- get_fixed 0
    def q_enable (c: ValidCircuit P P_Prime) (row: ℕ) :=
      if row = 0 ∨ row = 12 ∨ row = 24 ∨ row = 36 ∨ row = 48 ∨ row = 60 ∨
        row = 72 ∨ row = 84 ∨ row = 96 ∨ row = 108 ∨ row = 120 ∨
        row = 132 ∨ row = 144 ∨ row = 156 ∨ row = 168 ∨ row = 180 ∨
        row = 192 ∨ row = 204 ∨ row = 216 ∨ row = 228 ∨ row = 240 ∨
        row = 252 ∨ row = 264 ∨ row = 276 ∨ row = 288 ∨ row = 300 then 1
      else if row > 311 then c.1.FixedUnassigned 0 row
      else 0

    lemma fixed_0_q_enable (c: ValidCircuit P P_Prime): ∀ row: ℕ, fixed_func c 0 row = q_enable c row := by
      intro row
      match row with
        | x+312 => simp only [fixed_func, fixed_func_col_0, ge_iff_le, le_add_iff_nonneg_left,
          zero_le, Nat.reduceLeDiff, and_false, ↓reduceIte, Nat.reduceEqDiff, q_enable, or_self,
          gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
        | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
        | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl
        | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl | 24 => rfl | 25 => rfl | 26 => rfl | 27 => rfl | 28 => rfl | 29 => rfl
        | 30 => rfl | 31 => rfl | 32 => rfl | 33 => rfl | 34 => rfl | 35 => rfl | 36 => rfl | 37 => rfl | 38 => rfl | 39 => rfl
        | 40 => rfl | 41 => rfl | 42 => rfl | 43 => rfl | 44 => rfl | 45 => rfl | 46 => rfl | 47 => rfl | 48 => rfl | 49 => rfl
        | 50 => rfl | 51 => rfl | 52 => rfl | 53 => rfl | 54 => rfl | 55 => rfl | 56 => rfl | 57 => rfl | 58 => rfl | 59 => rfl
        | 60 => rfl | 61 => rfl | 62 => rfl | 63 => rfl | 64 => rfl | 65 => rfl | 66 => rfl | 67 => rfl | 68 => rfl | 69 => rfl
        | 70 => rfl | 71 => rfl | 72 => rfl | 73 => rfl | 74 => rfl | 75 => rfl | 76 => rfl | 77 => rfl | 78 => rfl | 79 => rfl
        | 80 => rfl | 81 => rfl | 82 => rfl | 83 => rfl | 84 => rfl | 85 => rfl | 86 => rfl | 87 => rfl | 88 => rfl | 89 => rfl
        | 90 => rfl | 91 => rfl | 92 => rfl | 93 => rfl | 94 => rfl | 95 => rfl | 96 => rfl | 97 => rfl | 98 => rfl | 99 => rfl
        | 100 => rfl | 101 => rfl | 102 => rfl | 103 => rfl | 104 => rfl | 105 => rfl | 106 => rfl | 107 => rfl | 108 => rfl | 109 => rfl
        | 120 => rfl | 111 => rfl | 112 => rfl | 113 => rfl | 114 => rfl | 115 => rfl | 116 => rfl | 117 => rfl | 118 => rfl | 119 => rfl
        | 110 => rfl | 121 => rfl | 122 => rfl | 123 => rfl | 124 => rfl | 125 => rfl | 126 => rfl | 127 => rfl | 128 => rfl | 129 => rfl
        | 130 => rfl | 131 => rfl | 132 => rfl | 133 => rfl | 134 => rfl | 135 => rfl | 136 => rfl | 137 => rfl | 138 => rfl | 139 => rfl
        | 140 => rfl | 141 => rfl | 142 => rfl | 143 => rfl | 144 => rfl | 145 => rfl | 146 => rfl | 147 => rfl | 148 => rfl | 149 => rfl
        | 150 => rfl | 151 => rfl | 152 => rfl | 153 => rfl | 154 => rfl | 155 => rfl | 156 => rfl | 157 => rfl | 158 => rfl | 159 => rfl
        | 160 => rfl | 161 => rfl | 162 => rfl | 163 => rfl | 164 => rfl | 165 => rfl | 166 => rfl | 167 => rfl | 168 => rfl | 169 => rfl
        | 170 => rfl | 171 => rfl | 172 => rfl | 173 => rfl | 174 => rfl | 175 => rfl | 176 => rfl | 177 => rfl | 178 => rfl | 179 => rfl
        | 180 => rfl | 181 => rfl | 182 => rfl | 183 => rfl | 184 => rfl | 185 => rfl | 186 => rfl | 187 => rfl | 188 => rfl | 189 => rfl
        | 190 => rfl | 191 => rfl | 192 => rfl | 193 => rfl | 194 => rfl | 195 => rfl | 196 => rfl | 197 => rfl | 198 => rfl | 199 => rfl
        | 200 => rfl | 201 => rfl | 202 => rfl | 203 => rfl | 204 => rfl | 205 => rfl | 206 => rfl | 207 => rfl | 208 => rfl | 209 => rfl
        | 210 => rfl | 211 => rfl | 212 => rfl | 213 => rfl | 214 => rfl | 215 => rfl | 216 => rfl | 217 => rfl | 218 => rfl | 219 => rfl
        | 220 => rfl | 221 => rfl | 222 => rfl | 223 => rfl | 224 => rfl | 225 => rfl | 226 => rfl | 227 => rfl | 228 => rfl | 229 => rfl
        | 230 => rfl | 231 => rfl | 232 => rfl | 233 => rfl | 234 => rfl | 235 => rfl | 236 => rfl | 237 => rfl | 238 => rfl | 239 => rfl
        | 240 => rfl | 241 => rfl | 242 => rfl | 243 => rfl | 244 => rfl | 245 => rfl | 246 => rfl | 247 => rfl | 248 => rfl | 249 => rfl
        | 250 => rfl | 251 => rfl | 252 => rfl | 253 => rfl | 254 => rfl | 255 => rfl | 256 => rfl | 257 => rfl | 258 => rfl | 259 => rfl
        | 260 => rfl | 261 => rfl | 262 => rfl | 263 => rfl | 264 => rfl | 265 => rfl | 266 => rfl | 267 => rfl | 268 => rfl | 269 => rfl
        | 270 => rfl | 271 => rfl | 272 => rfl | 273 => rfl | 274 => rfl | 275 => rfl | 276 => rfl | 277 => rfl | 278 => rfl | 279 => rfl
        | 280 => rfl | 281 => rfl | 282 => rfl | 283 => rfl | 284 => rfl | 285 => rfl | 286 => rfl | 287 => rfl | 288 => rfl | 289 => rfl
        | 290 => rfl | 291 => rfl | 292 => rfl | 293 => rfl | 294 => rfl | 295 => rfl | 296 => rfl | 297 => rfl | 298 => rfl | 299 => rfl
        | 300 => rfl | 301 => rfl | 302 => rfl | 303 => rfl | 304 => rfl | 305 => rfl | 306 => rfl | 307 => rfl | 308 => rfl | 309 => rfl
        | 310 => rfl
        | 311 => rfl

    lemma q_enable_at_round_start (c: ValidCircuit P P_Prime) (h_round: round ≤ 25):
      q_enable c (12*round) = 1 := by
        match round with
          | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
          | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl
          | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl | 24 => rfl | 25 => rfl | x+26 => aesop

    lemma q_enable_dvd (c: ValidCircuit P P_Prime) (hrow: row ≤ 311) (hrow_dvd: 12 ∣ row):
      q_enable c row = 1 := by
        unfold q_enable
        have hrow': ¬(row > 311) := not_lt.mpr hrow
        simp [hrow']
        have h: row = 12*(row/12)+row%12 := by exact Eq.symm (Nat.div_add_mod row 12)
        have h': row % 12 = 0 := by exact Nat.dvd_iff_mod_eq_zero.mp hrow_dvd
        rewrite [h', add_zero] at h
        generalize hround: row/12 = round
        rewrite [hround] at h
        subst h
        match round with
          | 0 => simp | 1 => simp | 2 => simp | 3 => simp
          | 4 => simp | 5 => simp | 6 => simp | 7 => simp
          | 8 => simp | 9 => simp | 10 => simp | 11 => simp
          | 12 => simp | 13 => simp | 14 => simp | 15 => simp
          | 16 => simp | 17 => simp | 18 => simp | 19 => simp
          | 20 => simp | 21 => simp | 22 => simp | 23 => simp
          | 24 => simp | 25 => simp | x+26 =>
            exfalso
            simp [mul_add] at hrow

    lemma q_enable_not_dvd (c: ValidCircuit P P_Prime) (hrow: row ≤ 311) (hrow_dvd: ¬ 12 ∣ row):
      q_enable c row = 0 := by
        unfold q_enable
        have hrow': ¬(row > 311) := not_lt.mpr hrow
        simp [hrow']
        intro h
        have h_contr: 12 ∣ row := by
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
          cases h with | inl h => subst h; decide | inr h =>
            subst h; decide
        contradiction


    def q_first (c: ValidCircuit P P_Prime) (row: ℕ) :=
      if row = 0 then 1
      else if row ≤ 311 then 0
      else c.1.FixedUnassigned 1 row

    lemma fixed_1_q_first (c: ValidCircuit P P_Prime): ∀ row: ℕ, fixed_func c 1 row = q_first c row := by
      intro row
      simp only [fixed_func, fixed_func_col_1, q_first]
      if h0: row = 0 then simp [h0]
      else simp [Nat.one_le_iff_ne_zero, h0]

    lemma q_first_zero (c: ValidCircuit P P_Prime): q_first c 0 = 1 := rfl

    -- get_fixed 2
    def q_round (c: ValidCircuit P P_Prime) (row: ℕ) :=
      if row = 12 ∨ row = 24 ∨ row = 36 ∨ row = 48 ∨ row = 60 ∨
        row = 72 ∨ row = 84 ∨ row = 96 ∨ row = 108 ∨ row = 120 ∨
        row = 132 ∨ row = 144 ∨ row = 156 ∨ row = 168 ∨ row = 180 ∨
        row = 192 ∨ row = 204 ∨ row = 216 ∨ row = 228 ∨ row = 240 ∨
        row = 252 ∨ row = 264 ∨ row = 276 ∨ row = 288 then 1
      else if row > 311 then c.1.FixedUnassigned 2 row
      else 0

    lemma fixed_2_q_round (c: ValidCircuit P P_Prime): ∀ row: ℕ, fixed_func c 2 row = q_round c row := by
      intro row
      match row with
        | x+312 => simp only [fixed_func, fixed_func_col_2, ge_iff_le, le_add_iff_nonneg_left,
          zero_le, Nat.reduceLeDiff, and_false, ↓reduceIte, Nat.reduceEqDiff, q_round, or_self,
          gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
        | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
        | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl
        | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl | 24 => rfl | 25 => rfl | 26 => rfl | 27 => rfl | 28 => rfl | 29 => rfl
        | 30 => rfl | 31 => rfl | 32 => rfl | 33 => rfl | 34 => rfl | 35 => rfl | 36 => rfl | 37 => rfl | 38 => rfl | 39 => rfl
        | 40 => rfl | 41 => rfl | 42 => rfl | 43 => rfl | 44 => rfl | 45 => rfl | 46 => rfl | 47 => rfl | 48 => rfl | 49 => rfl
        | 50 => rfl | 51 => rfl | 52 => rfl | 53 => rfl | 54 => rfl | 55 => rfl | 56 => rfl | 57 => rfl | 58 => rfl | 59 => rfl
        | 60 => rfl | 61 => rfl | 62 => rfl | 63 => rfl | 64 => rfl | 65 => rfl | 66 => rfl | 67 => rfl | 68 => rfl | 69 => rfl
        | 70 => rfl | 71 => rfl | 72 => rfl | 73 => rfl | 74 => rfl | 75 => rfl | 76 => rfl | 77 => rfl | 78 => rfl | 79 => rfl
        | 80 => rfl | 81 => rfl | 82 => rfl | 83 => rfl | 84 => rfl | 85 => rfl | 86 => rfl | 87 => rfl | 88 => rfl | 89 => rfl
        | 90 => rfl | 91 => rfl | 92 => rfl | 93 => rfl | 94 => rfl | 95 => rfl | 96 => rfl | 97 => rfl | 98 => rfl | 99 => rfl
        | 100 => rfl | 101 => rfl | 102 => rfl | 103 => rfl | 104 => rfl | 105 => rfl | 106 => rfl | 107 => rfl | 108 => rfl | 109 => rfl
        | 120 => rfl | 111 => rfl | 112 => rfl | 113 => rfl | 114 => rfl | 115 => rfl | 116 => rfl | 117 => rfl | 118 => rfl | 119 => rfl
        | 110 => rfl | 121 => rfl | 122 => rfl | 123 => rfl | 124 => rfl | 125 => rfl | 126 => rfl | 127 => rfl | 128 => rfl | 129 => rfl
        | 130 => rfl | 131 => rfl | 132 => rfl | 133 => rfl | 134 => rfl | 135 => rfl | 136 => rfl | 137 => rfl | 138 => rfl | 139 => rfl
        | 140 => rfl | 141 => rfl | 142 => rfl | 143 => rfl | 144 => rfl | 145 => rfl | 146 => rfl | 147 => rfl | 148 => rfl | 149 => rfl
        | 150 => rfl | 151 => rfl | 152 => rfl | 153 => rfl | 154 => rfl | 155 => rfl | 156 => rfl | 157 => rfl | 158 => rfl | 159 => rfl
        | 160 => rfl | 161 => rfl | 162 => rfl | 163 => rfl | 164 => rfl | 165 => rfl | 166 => rfl | 167 => rfl | 168 => rfl | 169 => rfl
        | 170 => rfl | 171 => rfl | 172 => rfl | 173 => rfl | 174 => rfl | 175 => rfl | 176 => rfl | 177 => rfl | 178 => rfl | 179 => rfl
        | 180 => rfl | 181 => rfl | 182 => rfl | 183 => rfl | 184 => rfl | 185 => rfl | 186 => rfl | 187 => rfl | 188 => rfl | 189 => rfl
        | 190 => rfl | 191 => rfl | 192 => rfl | 193 => rfl | 194 => rfl | 195 => rfl | 196 => rfl | 197 => rfl | 198 => rfl | 199 => rfl
        | 200 => rfl | 201 => rfl | 202 => rfl | 203 => rfl | 204 => rfl | 205 => rfl | 206 => rfl | 207 => rfl | 208 => rfl | 209 => rfl
        | 210 => rfl | 211 => rfl | 212 => rfl | 213 => rfl | 214 => rfl | 215 => rfl | 216 => rfl | 217 => rfl | 218 => rfl | 219 => rfl
        | 220 => rfl | 221 => rfl | 222 => rfl | 223 => rfl | 224 => rfl | 225 => rfl | 226 => rfl | 227 => rfl | 228 => rfl | 229 => rfl
        | 230 => rfl | 231 => rfl | 232 => rfl | 233 => rfl | 234 => rfl | 235 => rfl | 236 => rfl | 237 => rfl | 238 => rfl | 239 => rfl
        | 240 => rfl | 241 => rfl | 242 => rfl | 243 => rfl | 244 => rfl | 245 => rfl | 246 => rfl | 247 => rfl | 248 => rfl | 249 => rfl
        | 250 => rfl | 251 => rfl | 252 => rfl | 253 => rfl | 254 => rfl | 255 => rfl | 256 => rfl | 257 => rfl | 258 => rfl | 259 => rfl
        | 260 => rfl | 261 => rfl | 262 => rfl | 263 => rfl | 264 => rfl | 265 => rfl | 266 => rfl | 267 => rfl | 268 => rfl | 269 => rfl
        | 270 => rfl | 271 => rfl | 272 => rfl | 273 => rfl | 274 => rfl | 275 => rfl | 276 => rfl | 277 => rfl | 278 => rfl | 279 => rfl
        | 280 => rfl | 281 => rfl | 282 => rfl | 283 => rfl | 284 => rfl | 285 => rfl | 286 => rfl | 287 => rfl | 288 => rfl | 289 => rfl
        | 290 => rfl | 291 => rfl | 292 => rfl | 293 => rfl | 294 => rfl | 295 => rfl | 296 => rfl | 297 => rfl | 298 => rfl | 299 => rfl
        | 300 => rfl | 301 => rfl | 302 => rfl | 303 => rfl | 304 => rfl | 305 => rfl | 306 => rfl | 307 => rfl | 308 => rfl | 309 => rfl
        | 310 => rfl
        | 311 => rfl

    lemma q_round_at_round_start (c: ValidCircuit P P_Prime) (h_round: round ≤ 23):
      q_round c (12*(round+1)) = 1 := by
        match round with
          | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
          | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl
          | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl | x+24 => aesop

    --get_fixed 3
    lemma q_absorb_at_start_or_end (c: ValidCircuit P P_Prime) (h_round: round = 0 ∨ round = 25):
      fixed_func c 3 (12*round) = 1 := by
        cases h_round with
          | inl h => rewrite [h]; rfl
          | inr h => rewrite [h]; rfl

    lemma q_round_last_one (c: ValidCircuit P P_Prime):
      fixed_func c 4 300 = 1 := by rfl

    -- get_fixed 5
    def q_padding (c: ValidCircuit P P_Prime) (row: ℕ) :=
      if row = 12 ∨ row = 24 ∨ row = 36 ∨ row = 48 ∨ row = 60 ∨
        row = 72 ∨ row = 84 ∨ row = 96 ∨ row = 108 ∨ row = 120 ∨
        row = 132 ∨ row = 144 ∨ row = 156 ∨ row = 168 ∨ row = 180 ∨
        row = 192 ∨ row = 204 then 1
      else if row > 311 then c.1.FixedUnassigned 5 row
      else 0

    lemma fixed_5_q_padding (c: ValidCircuit P P_Prime): ∀ row: ℕ, fixed_func c 5 row = q_padding c row := by
      intro row
      match row with
        | x+312 => simp only [fixed_func, fixed_func_col_5, ge_iff_le, le_add_iff_nonneg_left,
          zero_le, Nat.reduceLeDiff, and_false, ↓reduceIte, Nat.reduceEqDiff, q_padding, or_self,
          gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
        | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
        | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl | 18 => rfl | 19 => rfl
        | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl | 24 => rfl | 25 => rfl | 26 => rfl | 27 => rfl | 28 => rfl | 29 => rfl
        | 30 => rfl | 31 => rfl | 32 => rfl | 33 => rfl | 34 => rfl | 35 => rfl | 36 => rfl | 37 => rfl | 38 => rfl | 39 => rfl
        | 40 => rfl | 41 => rfl | 42 => rfl | 43 => rfl | 44 => rfl | 45 => rfl | 46 => rfl | 47 => rfl | 48 => rfl | 49 => rfl
        | 50 => rfl | 51 => rfl | 52 => rfl | 53 => rfl | 54 => rfl | 55 => rfl | 56 => rfl | 57 => rfl | 58 => rfl | 59 => rfl
        | 60 => rfl | 61 => rfl | 62 => rfl | 63 => rfl | 64 => rfl | 65 => rfl | 66 => rfl | 67 => rfl | 68 => rfl | 69 => rfl
        | 70 => rfl | 71 => rfl | 72 => rfl | 73 => rfl | 74 => rfl | 75 => rfl | 76 => rfl | 77 => rfl | 78 => rfl | 79 => rfl
        | 80 => rfl | 81 => rfl | 82 => rfl | 83 => rfl | 84 => rfl | 85 => rfl | 86 => rfl | 87 => rfl | 88 => rfl | 89 => rfl
        | 90 => rfl | 91 => rfl | 92 => rfl | 93 => rfl | 94 => rfl | 95 => rfl | 96 => rfl | 97 => rfl | 98 => rfl | 99 => rfl
        | 100 => rfl | 101 => rfl | 102 => rfl | 103 => rfl | 104 => rfl | 105 => rfl | 106 => rfl | 107 => rfl | 108 => rfl | 109 => rfl
        | 120 => rfl | 111 => rfl | 112 => rfl | 113 => rfl | 114 => rfl | 115 => rfl | 116 => rfl | 117 => rfl | 118 => rfl | 119 => rfl
        | 110 => rfl | 121 => rfl | 122 => rfl | 123 => rfl | 124 => rfl | 125 => rfl | 126 => rfl | 127 => rfl | 128 => rfl | 129 => rfl
        | 130 => rfl | 131 => rfl | 132 => rfl | 133 => rfl | 134 => rfl | 135 => rfl | 136 => rfl | 137 => rfl | 138 => rfl | 139 => rfl
        | 140 => rfl | 141 => rfl | 142 => rfl | 143 => rfl | 144 => rfl | 145 => rfl | 146 => rfl | 147 => rfl | 148 => rfl | 149 => rfl
        | 150 => rfl | 151 => rfl | 152 => rfl | 153 => rfl | 154 => rfl | 155 => rfl | 156 => rfl | 157 => rfl | 158 => rfl | 159 => rfl
        | 160 => rfl | 161 => rfl | 162 => rfl | 163 => rfl | 164 => rfl | 165 => rfl | 166 => rfl | 167 => rfl | 168 => rfl | 169 => rfl
        | 170 => rfl | 171 => rfl | 172 => rfl | 173 => rfl | 174 => rfl | 175 => rfl | 176 => rfl | 177 => rfl | 178 => rfl | 179 => rfl
        | 180 => rfl | 181 => rfl | 182 => rfl | 183 => rfl | 184 => rfl | 185 => rfl | 186 => rfl | 187 => rfl | 188 => rfl | 189 => rfl
        | 190 => rfl | 191 => rfl | 192 => rfl | 193 => rfl | 194 => rfl | 195 => rfl | 196 => rfl | 197 => rfl | 198 => rfl | 199 => rfl
        | 200 => rfl | 201 => rfl | 202 => rfl | 203 => rfl | 204 => rfl | 205 => rfl | 206 => rfl | 207 => rfl | 208 => rfl | 209 => rfl
        | 210 => rfl | 211 => rfl | 212 => rfl | 213 => rfl | 214 => rfl | 215 => rfl | 216 => rfl | 217 => rfl | 218 => rfl | 219 => rfl
        | 220 => rfl | 221 => rfl | 222 => rfl | 223 => rfl | 224 => rfl | 225 => rfl | 226 => rfl | 227 => rfl | 228 => rfl | 229 => rfl
        | 230 => rfl | 231 => rfl | 232 => rfl | 233 => rfl | 234 => rfl | 235 => rfl | 236 => rfl | 237 => rfl | 238 => rfl | 239 => rfl
        | 240 => rfl | 241 => rfl | 242 => rfl | 243 => rfl | 244 => rfl | 245 => rfl | 246 => rfl | 247 => rfl | 248 => rfl | 249 => rfl
        | 250 => rfl | 251 => rfl | 252 => rfl | 253 => rfl | 254 => rfl | 255 => rfl | 256 => rfl | 257 => rfl | 258 => rfl | 259 => rfl
        | 260 => rfl | 261 => rfl | 262 => rfl | 263 => rfl | 264 => rfl | 265 => rfl | 266 => rfl | 267 => rfl | 268 => rfl | 269 => rfl
        | 270 => rfl | 271 => rfl | 272 => rfl | 273 => rfl | 274 => rfl | 275 => rfl | 276 => rfl | 277 => rfl | 278 => rfl | 279 => rfl
        | 280 => rfl | 281 => rfl | 282 => rfl | 283 => rfl | 284 => rfl | 285 => rfl | 286 => rfl | 287 => rfl | 288 => rfl | 289 => rfl
        | 290 => rfl | 291 => rfl | 292 => rfl | 293 => rfl | 294 => rfl | 295 => rfl | 296 => rfl | 297 => rfl | 298 => rfl | 299 => rfl
        | 300 => rfl | 301 => rfl | 302 => rfl | 303 => rfl | 304 => rfl | 305 => rfl | 306 => rfl | 307 => rfl | 308 => rfl | 309 => rfl
        | 310 => rfl
        | 311 => rfl

    lemma q_padding_at_round_start (c: ValidCircuit P P_Prime) (h_round: round ≤ 17) (hround_lower: round > 0):
      q_padding c (12*round) = 1 := by
        match round with
          | 0 => aesop | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
          | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl
          | x+18 => aesop

    lemma q_padding_late_rows (c: ValidCircuit P P_Prime) (hrow: row ≤ 311) (hrow_lower: row > 204):
      q_padding c row = 0 := by
        unfold q_padding
        rw [ite_cond_eq_false, ite_cond_eq_false]
        . simp [hrow]
        . aesop

    def q_padding_last (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P :=
      if row = 204 then 1
      else if row ≤ 311 then 0
      else c.1.FixedUnassigned 6 row

    lemma fixed_6_q_padding_last (c: ValidCircuit P P_Prime): ∀ row: ℕ, fixed_func c 6 row = q_padding_last c row := by
      intro row
      if h_row: row ≤ 203
      then {
        simp [fixed_func, fixed_func_col_6, h_row, q_padding_last]
        rw [ite_cond_eq_false, ite_cond_eq_true]
        . simp [le_trans h_row]
        . simp
          omega
      } else if h_row': row = 204 then {
        simp [h_row']
        rfl
      } else {
        have h_row'': 205 ≤ row := by
          have h: 204 ≤ row := by omega
          have h: 204 < row := lt_of_le_of_ne h (by aesop)
          omega
        if h_row''': row ≤ 311 then {
          simp [fixed_func, fixed_func_col_6, h_row, h_row', h_row'']
          rewrite [ite_cond_eq_true]
          simp [q_padding_last, h_row', h_row'', h_row''']
          simp [h_row''']
        } else {
          simp [fixed_func, fixed_func_col_6, h_row, h_row', h_row'', h_row''', q_padding_last]
        }
      }
  end Selectors

end Keccak
