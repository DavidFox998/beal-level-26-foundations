import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1150
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1151
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1152
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1153
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1154
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1155
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1156
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1157
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1158
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1159

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_115 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 115 + i)) (500 * (10 * 115 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1150
  by_cases h1 : i = 1
  · subst i
    exact chunk_1151
  by_cases h2 : i = 2
  · subst i
    exact chunk_1152
  by_cases h3 : i = 3
  · subst i
    exact chunk_1153
  by_cases h4 : i = 4
  · subst i
    exact chunk_1154
  by_cases h5 : i = 5
  · subst i
    exact chunk_1155
  by_cases h6 : i = 6
  · subst i
    exact chunk_1156
  by_cases h7 : i = 7
  · subst i
    exact chunk_1157
  by_cases h8 : i = 8
  · subst i
    exact chunk_1158
  by_cases h9 : i = 9
  · subst i
    exact chunk_1159
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
