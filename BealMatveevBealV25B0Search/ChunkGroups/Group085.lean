import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0850
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0851
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0852
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0853
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0854
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0855
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0856
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0857
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0858
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0859

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_085 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 85 + i)) (500 * (10 * 85 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0850
  by_cases h1 : i = 1
  · subst i
    exact chunk_0851
  by_cases h2 : i = 2
  · subst i
    exact chunk_0852
  by_cases h3 : i = 3
  · subst i
    exact chunk_0853
  by_cases h4 : i = 4
  · subst i
    exact chunk_0854
  by_cases h5 : i = 5
  · subst i
    exact chunk_0855
  by_cases h6 : i = 6
  · subst i
    exact chunk_0856
  by_cases h7 : i = 7
  · subst i
    exact chunk_0857
  by_cases h8 : i = 8
  · subst i
    exact chunk_0858
  by_cases h9 : i = 9
  · subst i
    exact chunk_0859
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
