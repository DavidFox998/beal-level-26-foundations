import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1210
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1211
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1212
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1213
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1214
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1215
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1216
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1217
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1218
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1219

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_121 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 121 + i)) (500 * (10 * 121 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1210
  by_cases h1 : i = 1
  · subst i
    exact chunk_1211
  by_cases h2 : i = 2
  · subst i
    exact chunk_1212
  by_cases h3 : i = 3
  · subst i
    exact chunk_1213
  by_cases h4 : i = 4
  · subst i
    exact chunk_1214
  by_cases h5 : i = 5
  · subst i
    exact chunk_1215
  by_cases h6 : i = 6
  · subst i
    exact chunk_1216
  by_cases h7 : i = 7
  · subst i
    exact chunk_1217
  by_cases h8 : i = 8
  · subst i
    exact chunk_1218
  by_cases h9 : i = 9
  · subst i
    exact chunk_1219
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
