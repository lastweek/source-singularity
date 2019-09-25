// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Corporation, Redmond, WA.
// author: Glenn Peterson
// 

// #define DEBUG_RESERVATIONS

using System;
using System.Collections;
//using System.Diagnostics;
//using System.Net.IP;

//using Microsoft.Singularity;

//using Drivers.Net;

//using NetStack.Common;
//using NetStack.NetDrivers;
//using NetStack.Protocols;

namespace NetStack.Runtime
{
    /// <summary>
    /// An enumeration describing a Reservation's current state: Under-, Over-,
    /// and Limit- Utilized.  It's used to control service to the Reservation's
    /// sessions.
    /// </summary>
    public enum ReservationCategory
    {
        /// <summary>
        /// This Reservation's Utilization is less than its "Reservation" level.
        /// </summary>
        /// <remarks>
        /// This reservation's sessions are serviced at high priority.
        /// </remarks>
        UnderUtilized = 0,

        /// <summary>
        /// This Reservation's Utilization is more than its "Reservation" level
        /// and less that its "Maximum" level.
        /// </summary>
        /// <remarks>
        /// This reservation's sessions are serviced at low priority.
        /// </remarks>
        OverUtilized = 1,

        /// <summary>
        /// This Reservation's Utilization is more than its "Maximum" level.
        /// </summary>
        /// <remarks>
        /// This reservation's sessions are not serviced.
        /// </remarks>
        LimitUtilized = 2,
    }

    /// <summary>
    /// A collection of Reservations of the same Category (Under/Over/Limit).
    /// </summary>
    internal class ReservationsByCategory
    {
        private ReservationCategory reservationCategory;
        private readonly ArrayList reservations = new ArrayList();

        public ReservationsByCategory(ReservationCategory reservationCategory)
        {
            this.reservationCategory = reservationCategory;
        }

        public ReservationCategory ReservationCategory
        {
            get { return this.reservationCategory; }
        }

        public void AddReservation(Reservation reservation)
        {
            this.reservations.Add(reservation);
        }

        public void RemoveReservation(Reservation reservation)
        {
            this.reservations.Remove(reservation);
        }
    }

    /// <summary>
    /// A Network Reservation, containing of a collection of Network Sessions.
    /// </summary>
    /// <remarks>
    /// In addition to the collection of sessions, a Reservation contains
    /// housekeeping information: currentUtilization, the time the
    /// currentUtilization was computed, Reservation category, and the
    /// utilization limits: Reserved and Maximum.  It also has the time
    /// (measured form the time the current utilization was computed) that
    /// it will become elegible to transfer to a more active category -
    /// assuming it remains idle if in the "OverUtilized" category.
    /// </remarks>
    internal class Reservation
    {
        public const double AveragingSeconds = 1.0;

//      public static TimeSpan AveragingTimeSpan =
//          TimeSpan.FromSeconds(Reservation.AveragingSeconds);

        // Sessions sharing this Reservation
        private readonly ArrayList sessions;

        // Utilization Limits for this Reservation.
        private double reservationUtilization;
        private double maximumUtilization;

        // Utilization and when Computed
        private double   currentUtilization;
        private DateTime currentUtilizationEvaluationTime;

        private ReservationsByCategory reservationsByCategory;

        public Reservation(double reservationUtilization,
                           double maximumUtilization)
        {
            // Initialize Readonly Fields
            this.sessions = new ArrayList();

            // Initialize Dynamic Fields
            this.reservationUtilization = reservationUtilization;
            this.maximumUtilization     = maximumUtilization;
            this.currentUtilization     = reservationUtilization * 0.5; // TODO: Revisit GRP
            this.currentUtilizationEvaluationTime = DateTime.Now;
        }

        public void AddSession(Session session)
        {
            this.sessions.Add(session);
        }

        public void RemoveSession(Session session)
        {
            this.sessions.Remove(session);
        }

        public void ChangeReservationLimits(double reservationUtilization,
                                            double maximumUtilization)
        {
            this.reservationUtilization = reservationUtilization;
            this.maximumUtilization = maximumUtilization;

            this.CheckCategory();
        }

        public void MergeUtilizationsWithDamping(double utilization,
                                                 TimeSpan duration)
        {
            // Compute the weighted (merged) utilization.
            double durationSeconds = duration.TotalSeconds;
            double mergedUtilization = this.currentUtilization * Reservation.AveragingSeconds
                                     + utilization * durationSeconds;

            // Rescale the merged Utilization and its Evaluation Time.
            this.currentUtilization =
                mergedUtilization * Reservation.AveragingSeconds /
                (durationSeconds + Reservation.AveragingSeconds);
            this.currentUtilizationEvaluationTime += duration;

            // See if we're in a new Category (Under/Over/Limit).
            this.CheckCategory();
        }

        private void CheckCategory()
        {
            ReservationCategory newCategory = ReservationCategory.UnderUtilized;

            if (this.currentUtilization > this.reservationUtilization)
            {
                newCategory = (this.currentUtilization > this.maximumUtilization)
                    ? ReservationCategory.OverUtilized : ReservationCategory.LimitUtilized;
            }

            if (newCategory != this.reservationsByCategory.ReservationCategory)
            {
                ChangeCategory(newCategory);
            }
        }

        private void ChangeCategory(ReservationCategory newCategory)
        {
            ReservationsByCategory newReservationsByCategory = new ReservationsByCategory(ReservationCategory.OverUtilized);   // BUGBUG: TODO: Look up in Array (GRP)

            this.reservationsByCategory.RemoveReservation(this);
            newReservationsByCategory.AddReservation(this);
            this.reservationsByCategory = newReservationsByCategory;
            
            if (newCategory == ReservationCategory.OverUtilized)
            {
                // Stur pot.  (Check appropriate queue - we may be able to start transmitting / receiving.  // TODO GRP.
            }
        }
    }
}
