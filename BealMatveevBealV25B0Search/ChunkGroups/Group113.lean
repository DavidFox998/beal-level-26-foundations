import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1130
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1131
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1132
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1133
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1134
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1135
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1136
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1137
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1138
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1139

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_113 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 113 + i)) (500 * (10 * 113 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1130
  by_cases h1 : i = 1
  · subst i
    exact chunk_1131
  by_cases h2 : i = 2
  · subst i
    exact chunk_1132
  by_cases h3 : i = 3
  · subst i
    exact chunk_1133
  by_cases h4 : i = 4
  · subst i
    exact chunk_1134
  by_cases h5 : i = 5
  · subst i
    exact chunk_1135
  by_cases h6 : i = 6
  · subst i
    exact chunk_1136
  by_cases h7 : i = 7
  · subst i
    exact chunk_1137
  by_cases h8 : i = 8
  · subst i
    exact chunk_1138
  by_cases h9 : i = 9
  · subst i
    exact chunk_1139
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
