import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 140 of the cap-17 certificate: slots 71680 .. 72191 -/
theorem chk_140 : chunkCheck 17 T stdSt 71680 512 = true := by decide +kernel

end Row17
