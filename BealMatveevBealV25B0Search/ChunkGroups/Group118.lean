import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1180
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1181
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1182
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1183
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1184
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1185
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1186
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1187
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1188
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1189

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_118 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 118 + i)) (500 * (10 * 118 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1180
  by_cases h1 : i = 1
  · subst i
    exact chunk_1181
  by_cases h2 : i = 2
  · subst i
    exact chunk_1182
  by_cases h3 : i = 3
  · subst i
    exact chunk_1183
  by_cases h4 : i = 4
  · subst i
    exact chunk_1184
  by_cases h5 : i = 5
  · subst i
    exact chunk_1185
  by_cases h6 : i = 6
  · subst i
    exact chunk_1186
  by_cases h7 : i = 7
  · subst i
    exact chunk_1187
  by_cases h8 : i = 8
  · subst i
    exact chunk_1188
  by_cases h9 : i = 9
  · subst i
    exact chunk_1189
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
