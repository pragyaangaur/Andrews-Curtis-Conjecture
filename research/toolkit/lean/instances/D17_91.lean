import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 91 of the cap-17 certificate: slots 46592 .. 47103 -/
theorem chk_91 : chunkCheck 17 T stdSt 46592 512 = true := by decide +kernel

end Row17
