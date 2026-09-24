import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1850
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1851
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1852
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1853
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1854
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1855
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1856
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1857
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1858
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1859

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_185 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 185 + i)) (500 * (10 * 185 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1850
  by_cases h1 : i = 1
  · subst i
    exact chunk_1851
  by_cases h2 : i = 2
  · subst i
    exact chunk_1852
  by_cases h3 : i = 3
  · subst i
    exact chunk_1853
  by_cases h4 : i = 4
  · subst i
    exact chunk_1854
  by_cases h5 : i = 5
  · subst i
    exact chunk_1855
  by_cases h6 : i = 6
  · subst i
    exact chunk_1856
  by_cases h7 : i = 7
  · subst i
    exact chunk_1857
  by_cases h8 : i = 8
  · subst i
    exact chunk_1858
  by_cases h9 : i = 9
  · subst i
    exact chunk_1859
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
