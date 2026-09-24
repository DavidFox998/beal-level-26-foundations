import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1020
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1021
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1022
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1023
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1024
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1025
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1026
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1027
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1028
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1029

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_102 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 102 + i)) (500 * (10 * 102 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1020
  by_cases h1 : i = 1
  · subst i
    exact chunk_1021
  by_cases h2 : i = 2
  · subst i
    exact chunk_1022
  by_cases h3 : i = 3
  · subst i
    exact chunk_1023
  by_cases h4 : i = 4
  · subst i
    exact chunk_1024
  by_cases h5 : i = 5
  · subst i
    exact chunk_1025
  by_cases h6 : i = 6
  · subst i
    exact chunk_1026
  by_cases h7 : i = 7
  · subst i
    exact chunk_1027
  by_cases h8 : i = 8
  · subst i
    exact chunk_1028
  by_cases h9 : i = 9
  · subst i
    exact chunk_1029
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
