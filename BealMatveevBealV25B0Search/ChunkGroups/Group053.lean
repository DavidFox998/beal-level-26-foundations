import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0530
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0531
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0532
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0533
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0534
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0535
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0536
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0537
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0538
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0539

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_053 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 53 + i)) (500 * (10 * 53 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0530
  by_cases h1 : i = 1
  · subst i
    exact chunk_0531
  by_cases h2 : i = 2
  · subst i
    exact chunk_0532
  by_cases h3 : i = 3
  · subst i
    exact chunk_0533
  by_cases h4 : i = 4
  · subst i
    exact chunk_0534
  by_cases h5 : i = 5
  · subst i
    exact chunk_0535
  by_cases h6 : i = 6
  · subst i
    exact chunk_0536
  by_cases h7 : i = 7
  · subst i
    exact chunk_0537
  by_cases h8 : i = 8
  · subst i
    exact chunk_0538
  by_cases h9 : i = 9
  · subst i
    exact chunk_0539
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
