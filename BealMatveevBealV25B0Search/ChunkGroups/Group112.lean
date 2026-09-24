import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1120
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1121
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1122
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1123
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1124
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1125
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1126
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1127
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1128
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1129

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_112 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 112 + i)) (500 * (10 * 112 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1120
  by_cases h1 : i = 1
  · subst i
    exact chunk_1121
  by_cases h2 : i = 2
  · subst i
    exact chunk_1122
  by_cases h3 : i = 3
  · subst i
    exact chunk_1123
  by_cases h4 : i = 4
  · subst i
    exact chunk_1124
  by_cases h5 : i = 5
  · subst i
    exact chunk_1125
  by_cases h6 : i = 6
  · subst i
    exact chunk_1126
  by_cases h7 : i = 7
  · subst i
    exact chunk_1127
  by_cases h8 : i = 8
  · subst i
    exact chunk_1128
  by_cases h9 : i = 9
  · subst i
    exact chunk_1129
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
