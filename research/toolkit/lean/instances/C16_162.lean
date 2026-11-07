import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 162 of the cap-16 certificate: slots 165888 .. 166911 -/
theorem chk_162 : chunkCheck 16 T stdSt 165888 1024 = true := by decide +kernel

end Row16
