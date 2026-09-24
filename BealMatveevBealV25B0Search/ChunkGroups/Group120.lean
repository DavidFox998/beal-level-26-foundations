import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1200
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1201
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1202
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1203
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1204
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1205
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1206
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1207
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1208
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1209

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_120 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 120 + i)) (500 * (10 * 120 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1200
  by_cases h1 : i = 1
  · subst i
    exact chunk_1201
  by_cases h2 : i = 2
  · subst i
    exact chunk_1202
  by_cases h3 : i = 3
  · subst i
    exact chunk_1203
  by_cases h4 : i = 4
  · subst i
    exact chunk_1204
  by_cases h5 : i = 5
  · subst i
    exact chunk_1205
  by_cases h6 : i = 6
  · subst i
    exact chunk_1206
  by_cases h7 : i = 7
  · subst i
    exact chunk_1207
  by_cases h8 : i = 8
  · subst i
    exact chunk_1208
  by_cases h9 : i = 9
  · subst i
    exact chunk_1209
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
