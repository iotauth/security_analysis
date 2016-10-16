# Formal Security Analysis for the Secure Swarm Toolkit (SST)

Authors: Hokeun Kim, Eunsuk Kang, Edward Lee, David Bronman__
Contact: hokeunkim@eecs.berkeley.edu or eunsuk.kang@berkeley.edu

## Introduction 

This repository contains a model of the authentication and authorization protocol in the Secure Swarm Toolkit (SST) in Alloy. Alloy is a formal modeling language based on a first-order relational logic with transitive closure. The underlying analysis engine, the Alloy Aanlyzer, can be used to perform simulation and automatic verification of a model against various types of properties, including security. The Alloy Analyzer is available for download at alloy.mit.edu.

We''ve performed a verification of the SST protocol model to check whether it satisfies the confidentiality and authenticity of the communication among trusted entities on an SST network.

## Content of the repository:

model/
  Auth.als: An Alloy model of the SST protocol__
  Auth.thm: A custom visualization theme for the Alloy model__
  
  
