import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1170
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1171
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1172
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1173
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1174
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1175
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1176
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1177
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1178
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1179

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_117 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 117 + i)) (500 * (10 * 117 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1170
  by_cases h1 : i = 1
  · subst i
    exact chunk_1171
  by_cases h2 : i = 2
  · subst i
    exact chunk_1172
  by_cases h3 : i = 3
  · subst i
    exact chunk_1173
  by_cases h4 : i = 4
  · subst i
    exact chunk_1174
  by_cases h5 : i = 5
  · subst i
    exact chunk_1175
  by_cases h6 : i = 6
  · subst i
    exact chunk_1176
  by_cases h7 : i = 7
  · subst i
    exact chunk_1177
  by_cases h8 : i = 8
  · subst i
    exact chunk_1178
  by_cases h9 : i = 9
  · subst i
    exact chunk_1179
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
