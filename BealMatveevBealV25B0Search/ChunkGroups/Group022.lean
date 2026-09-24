import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0220
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0221
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0222
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0223
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0224
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0225
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0226
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0227
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0228
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0229

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_022 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 22 + i)) (500 * (10 * 22 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0220
  by_cases h1 : i = 1
  · subst i
    exact chunk_0221
  by_cases h2 : i = 2
  · subst i
    exact chunk_0222
  by_cases h3 : i = 3
  · subst i
    exact chunk_0223
  by_cases h4 : i = 4
  · subst i
    exact chunk_0224
  by_cases h5 : i = 5
  · subst i
    exact chunk_0225
  by_cases h6 : i = 6
  · subst i
    exact chunk_0226
  by_cases h7 : i = 7
  · subst i
    exact chunk_0227
  by_cases h8 : i = 8
  · subst i
    exact chunk_0228
  by_cases h9 : i = 9
  · subst i
    exact chunk_0229
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
