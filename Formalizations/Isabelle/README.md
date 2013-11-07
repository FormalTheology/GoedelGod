Goedel's Ontological Proof in Isabelle
======================================

Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo


This directory contains a development of Goedel's ontological argument
(and some further results) in Isabelle/HOL (http://isabelle.in.tum.de/).

The two files presented here are:

- GoedelGod.thy: A development of Goedel's ontological argument with
  Sledgehammer (supported by LEO-II and Satallax) and Metis. Some
  additional lammata are needed.

- GoedelGodVarying.thy: The same as above, but this time for varying
  domain quantification (for individuals)

The files GoedelGod.thy and GoedelGodVarying.thy are meanwhile
outdated and there are new Isabelle/HOL versions of the proof
available in the subdirectory GoedelGodSession. These new versions
avoid the additional lemmata and they also study some additional aspects
such as the modal collapse, monotheism, flawlessness, and postive and
negative properties.

Best regards,
   Christoph Benzmueller and Bruno Woltzenlogel-Paleo


