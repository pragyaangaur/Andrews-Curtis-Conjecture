import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 152 of the cap-17 certificate: slots 77824 .. 78335 -/
theorem chk_152 : chunkCheck 17 T stdSt 77824 512 = true := by decide +kernel

end Row17
