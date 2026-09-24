import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1900
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1901
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1902
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1903
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1904
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1905
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1906
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1907
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1908
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1909

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_190 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 190 + i)) (500 * (10 * 190 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1900
  by_cases h1 : i = 1
  · subst i
    exact chunk_1901
  by_cases h2 : i = 2
  · subst i
    exact chunk_1902
  by_cases h3 : i = 3
  · subst i
    exact chunk_1903
  by_cases h4 : i = 4
  · subst i
    exact chunk_1904
  by_cases h5 : i = 5
  · subst i
    exact chunk_1905
  by_cases h6 : i = 6
  · subst i
    exact chunk_1906
  by_cases h7 : i = 7
  · subst i
    exact chunk_1907
  by_cases h8 : i = 8
  · subst i
    exact chunk_1908
  by_cases h9 : i = 9
  · subst i
    exact chunk_1909
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
