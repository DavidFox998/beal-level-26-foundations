import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1050
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1051
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1052
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1053
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1054
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1055
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1056
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1057
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1058
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1059

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_105 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 105 + i)) (500 * (10 * 105 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1050
  by_cases h1 : i = 1
  · subst i
    exact chunk_1051
  by_cases h2 : i = 2
  · subst i
    exact chunk_1052
  by_cases h3 : i = 3
  · subst i
    exact chunk_1053
  by_cases h4 : i = 4
  · subst i
    exact chunk_1054
  by_cases h5 : i = 5
  · subst i
    exact chunk_1055
  by_cases h6 : i = 6
  · subst i
    exact chunk_1056
  by_cases h7 : i = 7
  · subst i
    exact chunk_1057
  by_cases h8 : i = 8
  · subst i
    exact chunk_1058
  by_cases h9 : i = 9
  · subst i
    exact chunk_1059
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
