import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1240
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1241
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1242
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1243
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1244
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1245
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1246
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1247
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1248
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1249

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_124 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 124 + i)) (500 * (10 * 124 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1240
  by_cases h1 : i = 1
  · subst i
    exact chunk_1241
  by_cases h2 : i = 2
  · subst i
    exact chunk_1242
  by_cases h3 : i = 3
  · subst i
    exact chunk_1243
  by_cases h4 : i = 4
  · subst i
    exact chunk_1244
  by_cases h5 : i = 5
  · subst i
    exact chunk_1245
  by_cases h6 : i = 6
  · subst i
    exact chunk_1246
  by_cases h7 : i = 7
  · subst i
    exact chunk_1247
  by_cases h8 : i = 8
  · subst i
    exact chunk_1248
  by_cases h9 : i = 9
  · subst i
    exact chunk_1249
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
