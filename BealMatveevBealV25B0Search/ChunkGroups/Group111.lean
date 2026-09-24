import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1110
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1111
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1112
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1113
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1114
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1115
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1116
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1117
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1118
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1119

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_111 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 111 + i)) (500 * (10 * 111 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1110
  by_cases h1 : i = 1
  · subst i
    exact chunk_1111
  by_cases h2 : i = 2
  · subst i
    exact chunk_1112
  by_cases h3 : i = 3
  · subst i
    exact chunk_1113
  by_cases h4 : i = 4
  · subst i
    exact chunk_1114
  by_cases h5 : i = 5
  · subst i
    exact chunk_1115
  by_cases h6 : i = 6
  · subst i
    exact chunk_1116
  by_cases h7 : i = 7
  · subst i
    exact chunk_1117
  by_cases h8 : i = 8
  · subst i
    exact chunk_1118
  by_cases h9 : i = 9
  · subst i
    exact chunk_1119
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
