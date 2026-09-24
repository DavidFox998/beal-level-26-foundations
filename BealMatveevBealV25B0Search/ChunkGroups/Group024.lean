import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0240
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0241
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0242
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0243
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0244
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0245
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0246
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0247
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0248
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0249

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_024 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 24 + i)) (500 * (10 * 24 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0240
  by_cases h1 : i = 1
  · subst i
    exact chunk_0241
  by_cases h2 : i = 2
  · subst i
    exact chunk_0242
  by_cases h3 : i = 3
  · subst i
    exact chunk_0243
  by_cases h4 : i = 4
  · subst i
    exact chunk_0244
  by_cases h5 : i = 5
  · subst i
    exact chunk_0245
  by_cases h6 : i = 6
  · subst i
    exact chunk_0246
  by_cases h7 : i = 7
  · subst i
    exact chunk_0247
  by_cases h8 : i = 8
  · subst i
    exact chunk_0248
  by_cases h9 : i = 9
  · subst i
    exact chunk_0249
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
