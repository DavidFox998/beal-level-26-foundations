import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1230
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1231
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1232
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1233
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1234
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1235
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1236
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1237
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1238
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1239

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_123 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 123 + i)) (500 * (10 * 123 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1230
  by_cases h1 : i = 1
  · subst i
    exact chunk_1231
  by_cases h2 : i = 2
  · subst i
    exact chunk_1232
  by_cases h3 : i = 3
  · subst i
    exact chunk_1233
  by_cases h4 : i = 4
  · subst i
    exact chunk_1234
  by_cases h5 : i = 5
  · subst i
    exact chunk_1235
  by_cases h6 : i = 6
  · subst i
    exact chunk_1236
  by_cases h7 : i = 7
  · subst i
    exact chunk_1237
  by_cases h8 : i = 8
  · subst i
    exact chunk_1238
  by_cases h9 : i = 9
  · subst i
    exact chunk_1239
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
