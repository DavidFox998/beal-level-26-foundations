import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0050
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0051
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0052
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0053
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0054
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0055
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0056
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0057
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0058
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0059

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_005 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 5 + i)) (500 * (10 * 5 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0050
  by_cases h1 : i = 1
  · subst i
    exact chunk_0051
  by_cases h2 : i = 2
  · subst i
    exact chunk_0052
  by_cases h3 : i = 3
  · subst i
    exact chunk_0053
  by_cases h4 : i = 4
  · subst i
    exact chunk_0054
  by_cases h5 : i = 5
  · subst i
    exact chunk_0055
  by_cases h6 : i = 6
  · subst i
    exact chunk_0056
  by_cases h7 : i = 7
  · subst i
    exact chunk_0057
  by_cases h8 : i = 8
  · subst i
    exact chunk_0058
  by_cases h9 : i = 9
  · subst i
    exact chunk_0059
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
