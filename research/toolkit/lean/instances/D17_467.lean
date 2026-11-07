import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 467 of the cap-17 certificate: slots 239104 .. 239615 -/
theorem chk_467 : chunkCheck 17 T stdSt 239104 512 = true := by decide +kernel

end Row17
