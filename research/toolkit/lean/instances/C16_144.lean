import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 144 of the cap-16 certificate: slots 147456 .. 148479 -/
theorem chk_144 : chunkCheck 16 T stdSt 147456 1024 = true := by decide +kernel

end Row16
