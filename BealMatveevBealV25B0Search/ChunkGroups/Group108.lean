import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1080
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1081
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1082
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1083
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1084
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1085
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1086
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1087
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1088
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1089

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_108 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 108 + i)) (500 * (10 * 108 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1080
  by_cases h1 : i = 1
  · subst i
    exact chunk_1081
  by_cases h2 : i = 2
  · subst i
    exact chunk_1082
  by_cases h3 : i = 3
  · subst i
    exact chunk_1083
  by_cases h4 : i = 4
  · subst i
    exact chunk_1084
  by_cases h5 : i = 5
  · subst i
    exact chunk_1085
  by_cases h6 : i = 6
  · subst i
    exact chunk_1086
  by_cases h7 : i = 7
  · subst i
    exact chunk_1087
  by_cases h8 : i = 8
  · subst i
    exact chunk_1088
  by_cases h9 : i = 9
  · subst i
    exact chunk_1089
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
