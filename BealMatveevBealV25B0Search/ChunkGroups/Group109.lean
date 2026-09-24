import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1090
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1091
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1092
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1093
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1094
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1095
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1096
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1097
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1098
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1099

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_109 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 109 + i)) (500 * (10 * 109 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1090
  by_cases h1 : i = 1
  · subst i
    exact chunk_1091
  by_cases h2 : i = 2
  · subst i
    exact chunk_1092
  by_cases h3 : i = 3
  · subst i
    exact chunk_1093
  by_cases h4 : i = 4
  · subst i
    exact chunk_1094
  by_cases h5 : i = 5
  · subst i
    exact chunk_1095
  by_cases h6 : i = 6
  · subst i
    exact chunk_1096
  by_cases h7 : i = 7
  · subst i
    exact chunk_1097
  by_cases h8 : i = 8
  · subst i
    exact chunk_1098
  by_cases h9 : i = 9
  · subst i
    exact chunk_1099
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
