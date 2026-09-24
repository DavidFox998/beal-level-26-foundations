import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0810
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0811
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0812
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0813
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0814
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0815
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0816
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0817
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0818
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0819

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_081 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 81 + i)) (500 * (10 * 81 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0810
  by_cases h1 : i = 1
  · subst i
    exact chunk_0811
  by_cases h2 : i = 2
  · subst i
    exact chunk_0812
  by_cases h3 : i = 3
  · subst i
    exact chunk_0813
  by_cases h4 : i = 4
  · subst i
    exact chunk_0814
  by_cases h5 : i = 5
  · subst i
    exact chunk_0815
  by_cases h6 : i = 6
  · subst i
    exact chunk_0816
  by_cases h7 : i = 7
  · subst i
    exact chunk_0817
  by_cases h8 : i = 8
  · subst i
    exact chunk_0818
  by_cases h9 : i = 9
  · subst i
    exact chunk_0819
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
