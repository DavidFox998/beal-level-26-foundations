import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0020
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0021
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0022
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0023
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0024
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0025
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0026
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0027
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0028
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0029

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_002 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 2 + i)) (500 * (10 * 2 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0020
  by_cases h1 : i = 1
  · subst i
    exact chunk_0021
  by_cases h2 : i = 2
  · subst i
    exact chunk_0022
  by_cases h3 : i = 3
  · subst i
    exact chunk_0023
  by_cases h4 : i = 4
  · subst i
    exact chunk_0024
  by_cases h5 : i = 5
  · subst i
    exact chunk_0025
  by_cases h6 : i = 6
  · subst i
    exact chunk_0026
  by_cases h7 : i = 7
  · subst i
    exact chunk_0027
  by_cases h8 : i = 8
  · subst i
    exact chunk_0028
  by_cases h9 : i = 9
  · subst i
    exact chunk_0029
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
