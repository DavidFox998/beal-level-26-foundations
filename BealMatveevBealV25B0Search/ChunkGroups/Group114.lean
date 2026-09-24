import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1140
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1141
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1142
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1143
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1144
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1145
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1146
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1147
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1148
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1149

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_114 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 114 + i)) (500 * (10 * 114 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1140
  by_cases h1 : i = 1
  · subst i
    exact chunk_1141
  by_cases h2 : i = 2
  · subst i
    exact chunk_1142
  by_cases h3 : i = 3
  · subst i
    exact chunk_1143
  by_cases h4 : i = 4
  · subst i
    exact chunk_1144
  by_cases h5 : i = 5
  · subst i
    exact chunk_1145
  by_cases h6 : i = 6
  · subst i
    exact chunk_1146
  by_cases h7 : i = 7
  · subst i
    exact chunk_1147
  by_cases h8 : i = 8
  · subst i
    exact chunk_1148
  by_cases h9 : i = 9
  · subst i
    exact chunk_1149
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
